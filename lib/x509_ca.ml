open X509_certificate

open Asn_grammars

include X509_request_types

let raw_sign raw digest key =
  let hash = Nocrypto.Hash.digest digest raw in
  let sigval = pkcs1_digest_info_to_cstruct (digest, hash) in
  match key with
    | `RSA priv -> Nocrypto.Rsa.PKCS1.sig_encode ~key:priv sigval

type signing_request = CertificateRequest.certificate_request * Cstruct.t option

let info (sr, _) = sr.CertificateRequest.info

let validate_signature ({ CertificateRequest.info ; signature ; signature_algorithm }, raw) =
  let raw = match raw with
    | None -> CertificateRequest.certificate_request_info_to_cs info
    | Some x -> raw_cert_hack x signature
  in
  validate_raw_signature
    raw
    signature_algorithm
    signature
    info.public_key

let parse_signing_request cs =
  match CertificateRequest.certificate_request_of_cs cs with
  | Some csr when validate_signature (csr, Some cs) ->
    Some (csr, Some cs)
  | _ -> None

let cs_of_signing_request (csr, raw) =
  match raw with
  | Some x -> x
  | None -> CertificateRequest.certificate_request_to_cs csr

let request subject ?(digest = `SHA256) ?(extensions = []) = function
  | `RSA priv ->
    let public_key = `RSA (Nocrypto.Rsa.pub_of_priv priv) in
    (* TODO validate extensions, name constraints must match names etc *)
    let info : request_info = { subject ; public_key ; extensions } in
    let info_cs = CertificateRequest.certificate_request_info_to_cs info in
    let signature = raw_sign info_cs digest (`RSA priv) in
    let signature_algorithm = Algorithm.of_signature_algorithm `RSA digest in
    ({ CertificateRequest.info ; signature_algorithm ; signature }, None)

type violated_name_constraint = (* TODO is there a nicer way to express this? *)
  | Permitted of string
  | Excluded of string

type sign_result =
  | Certificate of t
  | Invalid_signing_request of signing_request (* TODO clarify name? "invalid self-signature?"*)
  | Violated_name_constraint of signing_request * violated_name_constraint
  | Invalid_issuer_certificate of certificate

let sign signing_request
    ~valid_from ~valid_until
    ?(digest = `SHA256)
    ?(serial = Nocrypto.(Rng.Z.gen_r Numeric.Z.one Numeric.Z.(one lsl 64)))
    ?(extensions = [])
    (key : private_key) (issuer : certificate) =
  if not (validate_ca_extensions issuer)
  then Invalid_issuer_certificate issuer
  else
  if not (validate_signature signing_request)
  then Invalid_signing_request signing_request
  else
  let signature_algo =
    Algorithm.of_signature_algorithm (private_key_to_keytype key) digest
  and info = (fst signing_request).CertificateRequest.info
  in
  let tbs_cert : tBSCertificate = {
      version = `V3 ;
      serial ;
      signature = signature_algo ;
      issuer = issuer.tbs_cert.issuer ;
      validity = (valid_from, valid_until) ;
      subject = info.subject ;
      pk_info = info.public_key ;
      issuer_id = None ;
      subject_id = None ;
      extensions
  } in
  let name_constraints_violated =
    let subject_names =
      begin match extensions |> List.find
      ( function
        | _ , `Subject_alt_name _ -> true
        | _ -> false
      ) with
      | _, `Subject_alt_name subj_alt_names ->
          (List.fold_left (fun acc -> function `CN n -> n::acc | _ -> acc) [] info.subject)
          @
          (List.fold_left (fun acc -> function `DNS n -> n::acc | _ -> acc) [] subj_alt_names)
      | _ -> []
      | exception Not_found ->
          (List.fold_left (fun acc -> function `CN n -> n::acc | _ -> acc) [] info.subject)
      end
    in
    (* validate that the CSR CN and DNS names are within the boundaries of issuer: *)
    validate_name_constraints (extn_name_constraints issuer) subject_names
    &&
    (extensions |> List.for_all
      ( function
        | ( _ , `Name_constraints ([], _))
        | ( _ , `Name_constraints ( _, []))
          -> false
          (* Implement: "Conforming CAs MUST NOT
           * issue certificates where name constraints is an empty sequence.
           * That  is, either the permittedSubtrees field or the excludedSubtrees
           * MUST be present." *)

      | ( _ , `Name_constraints (permitted_subtrees, excluded_subtrees )) as subject_constraints ->
          (* verify that the subject names of signing_request is within
           * the subject's own name_constraints: *)
          validate_name_constraints (Some subject_constraints) subject_names

          (* TODO MUST verify that subject's name constraints are within issuer's name constraints *)
      | _ -> true (* ignore extensions that are not `Name_constraints *)
     ))
  in
  if name_constraints_violated
  then Violated_name_constraint (signing_request , (Permitted "TODO")) (*(snd name_constraints_violated)*)
  else
  let tbs_raw = tbs_certificate_to_cstruct tbs_cert in
  let signature_val = raw_sign tbs_raw digest key in
  let asn = {
    tbs_cert ;
    signature_algo ;
    signature_val ;
  } in
  let raw = certificate_to_cstruct asn in
  Certificate { asn ; raw }
