Type ::= RANGE(1, 255)
	{SIZE_Type <- 1
	VAL_Type <- Func_hex_n_bytes_to_int_dsl($1$)}

Typecheck(VAL_Id) ::= Type
	{SIZE_Typecheck <- SIZE_Type
	VAL_Typecheck <- VAL_Type
	POSTCOND : VAL_Type = VAL_Id}

Length ::= Shortlength
	{SIZE_Length <- SIZE_Shortlength
	VAL_Length <- VAL_Shortlength}
	| Longlength
	{SIZE_Length <- SIZE_Longlength
	VAL_Length <- Func_hex_n_bytes_to_int_dsl(VAL_Longlength)
	POSTCOND : VAL_Length >= 128 }

Shortlength ::= RANGE(0, 127)
    { SIZE_Shortlength <- 1
    VAL_Shortlength <- Func_hex_n_bytes_to_int_dsl($1$)}

Longlength ::= Typelonglength Longlengthvalues(VAL_Typelonglength)
    { SIZE_Longlength <- SIZE_Typelonglength + SIZE_Longlengthvalues
    VAL_Longlength <- VAL_Longlengthvalues}

Typelonglength ::= RANGE(128, 255)
    { SIZE_Typelonglength <- 1
    VAL_Typelonglength <- Func_hex_n_bytes_to_int_dsl($1$) - 128}

Longlengthvalues(VAL_Typelonglength) ::= Bytee Longlengthvalues(VAL_Typelonglength - 1)
    { SIZE_Longlengthvalues <- SIZE_Bytee + SIZE_Longlengthvalues
    VAL_Longlengthvalues <- Func_addtotuple_dsl(VAL_Bytee, VAL_Longlengthvalues)
    PRECONDRET  : VAL_Typelonglength > 0}

Bytee ::= RANGE(0, 255)
	{ SIZE_Bytee <- 1
	VAL_Bytee <- $1$ }

Value(VAL_Length) ::= Bytee Value(VAL_Length - 1)
    { SIZE_Value <- SIZE_Bytee + SIZE_Value
    VAL_Value <- Func_addtotuple_dsl(VAL_Bytee, VAL_Value)
    PRECONDRET  : VAL_Length > 0}

Cert ::= Typecheck(48) Length Fieldscert
	{SIZE_Cert <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldscert
	VAL_Cert <- Func_Certificate(VAL_Fieldscert)
	POSTCOND : VAL_Length > 0 && SIZE_Fieldscert = VAL_Length && Func_endcheck(2) }

Fieldscert ::= Tbscert Signalgorithm Signature
	{SIZE_Fieldscert <- SIZE_Tbscert + SIZE_Signalgorithm + SIZE_Signature
	VAL_Fieldscert <- (VAL_Tbscert , VAL_Signalgorithm , VAL_Signature)
	POSTCOND : Func_endcheck(2) }

Tbscert ::= Typecheck(48) Length Fieldstbscert
	{SIZE_Tbscert <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldstbscert
	VAL_Tbscert <- Func_TbsCertificate(VAL_Fieldstbscert)
	POSTCOND : VAL_Length > 0 && SIZE_Fieldstbscert = VAL_Length && Func_endcheck(1) }

Signalgorithm ::= Typecheck(48) Length Fieldssignalgo(VAL_Length)
	{SIZE_Signalgorithm <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldssignalgo
	VAL_Signalgorithm <- Func_SignatureAlgorithm(VAL_Fieldssignalgo)
	POSTCOND : VAL_Length > 0 && SIZE_Fieldssignalgo = VAL_Length && Func_endcheck(1) }

Signature ::= Typecheck(3) Length Value(VAL_Length)
	{SIZE_Signature <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Signature <- Func_array_to_bytes_dsl(VAL_Value)
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length && Func_endcheck(2) }

Fieldstbscert ::= Version_? Serial Signalgo Issuer Validity Subject Subpubkeyinfo Issuniid_? Subuniid_? Extensions_?
	{SIZE_Fieldstbscert <- SIZE_Version + SIZE_Serial + SIZE_Signalgo + SIZE_Issuer + SIZE_Validity + SIZE_Subject + SIZE_Subpubkeyinfo + SIZE_Extensions + SIZE_Issuniid + SIZE_Subuniid
	VAL_Version <- Func_map_version(VAL_Version)
	VAL_Fieldstbscert <- (VAL_Version , VAL_Serial , VAL_Signalgo , VAL_Issuer , VAL_Validity , VAL_Subject , VAL_Subpubkeyinfo  , VAL_Issuniid , VAL_Subuniid, VAL_Extensions)
	POSTCOND : Func_endcheck(1) }

Version ::= Typecheck(160) Length Fieldsversion
	{SIZE_Version <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldsversion
	VAL_Version <- VAL_Fieldsversion
	POSTCOND : VAL_Length > 0 && SIZE_Fieldsversion = VAL_Length  && Func_endcheck(1) }

Fieldsversion ::= Typecheck(2) Length Value(VAL_Length)
	{SIZE_Fieldsversion <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Fieldsversion <- Func_hex_n_bytes_to_int_dsl(VAL_Value)
	VAL_Fieldsversion <- [VAL_Fieldsversion, SIZE_Value]
	POSTCOND : VAL_Length = 1 && SIZE_Value = VAL_Length  && Func_endcheck(1) }

Serial ::= Typecheck(2) Length Value(VAL_Length)
	{SIZE_Serial <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Serial <- Func_hex_n_bytes_to_int_dsl(VAL_Value)
	VAL_Serial <- [VAL_Serial, SIZE_Value]
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length  && Func_endcheck(1) }

Signalgo ::= Typecheck(48) Length Fieldssignalgo(VAL_Length)
	{SIZE_Signalgo <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldssignalgo
	VAL_Signalgo <- Func_SignatureAlgorithm(VAL_Fieldssignalgo)
	POSTCOND : VAL_Length > 0 && SIZE_Fieldssignalgo = VAL_Length  && Func_endcheck(1) }

Signoid ::= Typecheck(6) Length Value(VAL_Length)
	{SIZE_Signoid <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Signoid <- Func_hex_n_bytes_to_int_dsl(VAL_Value)
	VAL_Signoid <- [VAL_Signoid, SIZE_Value]
	POSTCOND : SIZE_Value = VAL_Length  && Func_endcheck(1) }

Signparam(VAL_Signoid, VAL_Lenthh) ::= Type Length Value(VAL_Length)
	{SIZE_Signparam <- SIZE_Type + SIZE_Length + SIZE_Value
	VAL_Value <- Func_array_to_bytes_dsl(VAL_Value)
	VAL_Signparam <- Func_Parameter(VAL_Type, VAL_Value)
	VAL_Signoid <- Func_getintvalue(VAL_Signoid)
	PRECONDRET : VAL_Lenthh > 0
	POSTCOND : SIZE_Value = VAL_Length && ((VAL_Type = 5 && VAL_Length = 0 && (VAL_Signoid = 784439383290839892228 || VAL_Signoid = 784439383290839892229 || VAL_Signoid = 784439383290839892235 || VAL_Signoid = 784439383290839892238 || VAL_Signoid = 784439383290839892236 || VAL_Signoid = 784439383290839892237 || VAL_Signoid = 784439383290839892234 || VAL_Signoid = 784439383290839892226 || VAL_Signoid = 784439383290839892227)) || (VAL_Signoid != 784439383290839892228 && VAL_Signoid != 784439383290839892229 && VAL_Signoid != 784439383290839892235 && VAL_Signoid != 784439383290839892238 && VAL_Signoid != 784439383290839892236 && VAL_Signoid != 784439383290839892237 && VAL_Signoid != 784439383290839892234 && VAL_Signoid != 784439383290839892226 && VAL_Signoid != 784439383290839892227)) && Func_endcheck(1) }

Signparampk(VAL_Signoid, VAL_Lenthh) ::= Type Length Value(VAL_Length)
	{SIZE_Signparampk <- SIZE_Type + SIZE_Length + SIZE_Value
	VAL_Value <- Func_array_to_bytes_dsl(VAL_Value)
	VAL_Signparampk <- Func_Parameter(VAL_Type, VAL_Value)
	VAL_Signoid <- Func_getintvalue(VAL_Signoid)
	PRECONDRET : VAL_Lenthh > 0
	POSTCOND : SIZE_Value = VAL_Length && ((VAL_Type = 5 && VAL_Length = 0 && VAL_Signoid = 784439383290839892225) || VAL_Signoid != 784439383290839892225) && Func_endcheck(1) }

Issuer ::= Typecheck(48) Length Rdnsets(VAL_Length)
	{SIZE_Issuer <- SIZE_Typecheck + SIZE_Length + SIZE_Rdnsets
	VAL_Issuer <- Func_splituple(VAL_Rdnsets)
	VAL_Issuer <- Func_IssuerDN(VAL_Issuer)
	POSTCOND : SIZE_Rdnsets = VAL_Length  && Func_endcheck(1) }

Validity ::= Typecheck(48) Length Fieldsvalidity
	{SIZE_Validity <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldsvalidity
	VAL_Validity <- VAL_Fieldsvalidity
	POSTCOND : VAL_Length > 0 && SIZE_Fieldsvalidity = VAL_Length  && Func_endcheck(1) }

Fieldsvalidity ::= Notbefore Notafter
	{SIZE_Fieldsvalidity <- SIZE_Notbefore + SIZE_Notafter
	VAL_Fieldsvalidity <- Func_ValidityPeriod(VAL_Notbefore , VAL_Notafter )
	POSTCOND : Func_endcheck(1) }

Subject ::= Typecheck(48) Length Rdnsets(VAL_Length)
	{SIZE_Subject <- SIZE_Typecheck + SIZE_Length + SIZE_Rdnsets
	VAL_Subject <- Func_splituple(VAL_Rdnsets)
	VAL_Subject <- Func_SubjectDN(VAL_Subject)
	POSTCOND : SIZE_Rdnsets = VAL_Length  && Func_endcheck(1) }

Subpubkeyinfo ::= Typecheck(48) Length Fieldssubpki
	{SIZE_Subpubkeyinfo <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldssubpki
	VAL_Subpubkeyinfo <- VAL_Fieldssubpki
	POSTCOND : VAL_Length > 0 && SIZE_Fieldssubpki = VAL_Length  && Func_endcheck(1) }

Fieldssubpki ::= Signalgopk Publickey
	{SIZE_Fieldssubpki <- SIZE_Signalgopk + SIZE_Publickey
	VAL_Fieldssubpki <- Func_SubjectPKI(VAL_Signalgopk , VAL_Publickey )
	POSTCOND : Func_endcheck(1) }

Signalgopk ::= Typecheck(48) Length Fieldssignalgopk(VAL_Length)
	{SIZE_Signalgopk <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldssignalgopk
	VAL_Signalgopk <- VAL_Fieldssignalgopk
	POSTCOND : VAL_Length > 0 && SIZE_Fieldssignalgopk = VAL_Length  && Func_endcheck(1) }

Publickey ::= Typecheck(3) Length 0 Publickeyopts(VAL_Length - 1)
	{SIZE_Publickey <- SIZE_Typecheck + SIZE_Length + 1 + SIZE_Publickeyopts
	VAL_Publickey <- VAL_Publickeyopts
	POSTCOND : VAL_Length > 0 && 1 + SIZE_Publickeyopts = VAL_Length  && Func_endcheck(1) }

Publickeyopts(VAL_Length) ::= Publickeyrsa
	{SIZE_Publickeyopts <- SIZE_Publickeyrsa
	VAL_Publickeyopts <- VAL_Publickeyrsa
	POSTCOND : Func_endcheck(1) }
	| Publickeyothers(VAL_Length)
	{SIZE_Publickeyopts <- SIZE_Publickeyothers
	VAL_Publickeyopts <- VAL_Publickeyothers
	POSTCOND : Func_endcheck(1) }

Publickeyrsa ::= Typecheck(48) Length Fieldspublickeyrsa
	{SIZE_Publickeyrsa <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldspublickeyrsa
	VAL_Publickeyrsa <- VAL_Fieldspublickeyrsa
	POSTCOND : VAL_Length > 0 && SIZE_Fieldspublickeyrsa = VAL_Length  && Func_endcheck(1) }

Publickeyothers(VAL_Length) ::= Value(VAL_Length)
	{SIZE_Publickeyothers <- SIZE_Value
	VAL_Publickeyothers <- Func_addtotuple_dsl(0, VAL_Value)
	VAL_Publickeyothers <- Func_array_to_bytes_dsl(VAL_Publickeyothers)
	POSTCOND : VAL_Length > 0  && Func_endcheck(1) }

Fieldspublickeyrsa ::= Rsan Rsae
    { SIZE_Fieldspublickeyrsa <- SIZE_Rsae + SIZE_Rsan
    VAL_Fieldspublickeyrsa <- Func_RSAkey(VAL_Rsan, VAL_Rsae)
    PRECONDRET  : Func_endcheck(1)}

Rsae ::= Typecheck(2) Length Value(VAL_Length)
	{SIZE_Rsae <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Rsae <- Func_hex_n_bytes_to_int_dsl(VAL_Value)
	VAL_Rsae <- [VAL_Rsae, SIZE_Value]
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length  && Func_endcheck(1) }

Rsan ::= Typecheck(2) Length Value(VAL_Length)
	{SIZE_Rsan <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Rsan <- Func_hex_n_bytes_to_int_dsl(VAL_Value)
	VAL_Rsan <- [VAL_Rsan, SIZE_Value]
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length  && Func_endcheck(1) }

Issuniid ::= Typecheck(161) Length Value(VAL_Length)
	{SIZE_Issuniid <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Issuniid <- Func_array_to_bytes_dsl(VAL_Value)
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length  && Func_endcheck(1) }

Subuniid ::= Typecheck(162) Length Value(VAL_Length)
	{SIZE_Subuniid <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Subuniid <- Func_array_to_bytes_dsl(VAL_Value)
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length  && Func_endcheck(1) }

Extensions ::= Typecheck(163) Length Extensionsseq
	{SIZE_Extensions <- SIZE_Typecheck + SIZE_Length + SIZE_Extensionsseq
	VAL_Extensions <- Func_Extns(VAL_Extensionsseq)
	POSTCOND : SIZE_Extensionsseq = VAL_Length  && Func_endcheck(1) }

Extensionsseq ::= Typecheck(48) Length Fieldsextensionsseq(VAL_Length)
	{SIZE_Extensionsseq <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldsextensionsseq
	VAL_Extensionsseq <- Func_splituple(VAL_Fieldsextensionsseq)
	POSTCOND : VAL_Length > 0 && SIZE_Fieldsextensionsseq = VAL_Length  && Func_endcheck(1) }

Fieldsextensionsseq(VAL_Length) ::= Extension Fieldsextensionsseq(VAL_Length - SIZE_Extension)
    { SIZE_Fieldsextensionsseq <- SIZE_Extension + SIZE_Fieldsextensionsseq
    VAL_Fieldsextensionsseq<- (VAL_Extension, VAL_Fieldsextensionsseq)
    PRECONDRET  : VAL_Length > 0}

Extension ::= Typecheck(48) Length Extnidgen Critical_? Extensionsoption(VAL_Extnidgen, VAL_Critical)
	{ SIZE_Extension <- SIZE_Typecheck + SIZE_Length + SIZE_Extnidgen + SIZE_Critical + SIZE_Extensionsoption
	VAL_Extension <- VAL_Extensionsoption
	POSTCOND : SIZE_Extnidgen + SIZE_Critical + SIZE_Extensionsoption = VAL_Length  && Func_endcheck(1) }

Extensionsoption(VAL_Extnidgen, VAL_Critical) ::= Fieldsextensionaki(VAL_Extnidgen, VAL_Critical)
	{SIZE_Extensionsoption <- SIZE_Fieldsextensionaki
	VAL_Extensionsoption <- VAL_Fieldsextensionaki
	PRECONDENT : Func_getintvalue(VAL_Extnidgen) = 5578019 }
	| Fieldsextensionski(VAL_Extnidgen, VAL_Critical)
	{SIZE_Extensionsoption <- SIZE_Fieldsextensionski
	VAL_Extensionsoption <- VAL_Fieldsextensionski
	PRECONDENT : Func_getintvalue(VAL_Extnidgen) = 5577998 }
	| Fieldsextensionsku(VAL_Extnidgen, VAL_Critical)
	{SIZE_Extensionsoption <- SIZE_Fieldsextensionsku
	VAL_Extensionsoption <- VAL_Fieldsextensionsku
	PRECONDENT : Func_getintvalue(VAL_Extnidgen) = 5577999 }
	| Fieldsextensionseku(VAL_Extnidgen, VAL_Critical)
	{SIZE_Extensionsoption <- SIZE_Fieldsextensionseku
	VAL_Extensionsoption <- VAL_Fieldsextensionseku
	PRECONDENT : Func_getintvalue(VAL_Extnidgen) = 5578021 }
	| Fieldsextensionsbc(VAL_Extnidgen, VAL_Critical)
	{SIZE_Extensionsoption <- SIZE_Fieldsextensionsbc
	VAL_Extensionsoption <- VAL_Fieldsextensionsbc
	PRECONDENT : Func_getintvalue(VAL_Extnidgen) = 5578003 }
	| Fieldsextensionssan(VAL_Extnidgen, VAL_Critical)
	{SIZE_Extensionsoption <- SIZE_Fieldsextensionssan
	VAL_Extensionsoption <- VAL_Fieldsextensionssan
	PRECONDENT : Func_getintvalue(VAL_Extnidgen) = 5578001 }
	| Fieldsextensionsian(VAL_Extnidgen, VAL_Critical)
	{SIZE_Extensionsoption <- SIZE_Fieldsextensionsian
	VAL_Extensionsoption <- VAL_Fieldsextensionsian
	PRECONDENT : Func_getintvalue(VAL_Extnidgen) = 5578002 }
	| Fieldsextensionscertpol(VAL_Extnidgen, VAL_Critical)
	{SIZE_Extensionsoption <- SIZE_Fieldsextensionscertpol
	VAL_Extensionsoption <- VAL_Fieldsextensionscertpol
	PRECONDENT : Func_getintvalue(VAL_Extnidgen) = 5578016 }
	| Fieldsextensionscrldist(VAL_Extnidgen, VAL_Critical)
	{SIZE_Extensionsoption <- SIZE_Fieldsextensionscrldist
	VAL_Extensionsoption <- VAL_Fieldsextensionscrldist
	PRECONDENT : Func_getintvalue(VAL_Extnidgen) = 5578015 }
	| Fieldsextensionsaia(VAL_Extnidgen, VAL_Critical)
	{SIZE_Extensionsoption <- SIZE_Fieldsextensionsaia
	VAL_Extensionsoption <- VAL_Fieldsextensionsaia
	PRECONDENT : Func_getintvalue(VAL_Extnidgen) = 3100166514561974529 }
	| Fieldsextension(VAL_Extnidgen, VAL_Critical)
	{SIZE_Extensionsoption <- SIZE_Fieldsextension
	VAL_Extensionsoption <- VAL_Fieldsextension
	PRECONDENT : Func_getintvalue(VAL_Extnidgen) != 5578019 && Func_getintvalue(VAL_Extnidgen) != 5577998 && Func_getintvalue(VAL_Extnidgen) != 5577999 && Func_getintvalue(VAL_Extnidgen) != 5578021 && Func_getintvalue(VAL_Extnidgen) != 5578003 && Func_getintvalue(VAL_Extnidgen) != 5578001 && Func_getintvalue(VAL_Extnidgen) != 5578002 && Func_getintvalue(VAL_Extnidgen) != 5578016 && Func_getintvalue(VAL_Extnidgen) != 5578015 && Func_getintvalue(VAL_Extnidgen) != 3100166514561974529 }

Fieldsextension(VAL_Extnidgen, VAL_Critical) ::= Extnvalue
	{SIZE_Fieldsextension <- SIZE_Extnvalue
	VAL_Critical <- Func_map_bool(VAL_Critical)
	VAL_Extnvalue <- Func_Unknown_extension(VAL_Extnvalue)
	VAL_Fieldsextension <- Func_Extn(VAL_Extnidgen, VAL_Critical , VAL_Extnvalue)
	POSTCOND : Func_endcheck(1) }

Extnidgen ::= Typecheck(6) Length Value(VAL_Length)
	{SIZE_Extnidgen <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Extnidgen <- Func_hex_n_bytes_to_int_dsl(VAL_Value)
	VAL_Extnidgen <- [VAL_Extnidgen, SIZE_Extnidgen]
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length  && Func_endcheck(1) }

Extnvalue ::= Typecheck(4) Length Value(VAL_Length)
	{SIZE_Extnvalue <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Extnvalue <- Func_array_to_bytes_dsl(VAL_Value)
	POSTCOND : SIZE_Value = VAL_Length  && Func_endcheck(1) }

Fieldsextensionaki(VAL_Extnid, VAL_Critical) ::= Authkeyid
	{SIZE_Fieldsextensionaki <- SIZE_Authkeyid
	VAL_Critical <- Func_map_bool(VAL_Critical)
	VAL_Fieldsextensionaki <- Func_Extn(VAL_Extnid, VAL_Critical , VAL_Authkeyid)
	POSTCOND : Func_endcheck(1) }

Authkeyid ::= Typecheck(4) Length Fieldsaki
	{SIZE_Authkeyid <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldsaki
	VAL_Authkeyid <- VAL_Fieldsaki
	POSTCOND : VAL_Length > 0 && SIZE_Fieldsaki = VAL_Length  && Func_endcheck(1) }

Fieldsaki ::= Typecheck(48) Length Fieldsakiseq
	{SIZE_Fieldsaki <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldsakiseq
	VAL_Fieldsaki <- VAL_Fieldsakiseq
	POSTCOND : VAL_Length > 0 && SIZE_Fieldsakiseq = VAL_Length  && Func_endcheck(1) }

Fieldsakiseq ::= Keyid_? Authcertissuer_? Authcertserial_?
	{SIZE_Fieldsakiseq <- SIZE_Keyid + SIZE_Authcertissuer + SIZE_Authcertserial
	VAL_Fieldsakiseq <- Func_Auth_key_id(VAL_Keyid , VAL_Authcertissuer, VAL_Authcertserial)
	POSTCOND : Func_endcheck(1) }

Keyid ::= Typecheck(128) Length Value(VAL_Length)
	{SIZE_Keyid <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Keyid <- Func_hex_n_bytes_to_int_dsl(VAL_Value)
	VAL_Keyid <- [VAL_Keyid, SIZE_Value]
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length  && Func_endcheck(1) }

Authcertissuer ::= Typecheck(161) Length Fieldsauthcertissuer
	{SIZE_Authcertissuer <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldsauthcertissuer
	VAL_Authcertissuer <- VAL_Fieldsauthcertissuer
	POSTCOND : VAL_Length > 0 && SIZE_Fieldsauthcertissuer = VAL_Length  && Func_endcheck(1) }

Fieldsauthcertissuer ::= Typecheck(48) Length Fieldsaltname(VAL_Length)
	{SIZE_Fieldsauthcertissuer <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldsaltname
	VAL_Fieldsauthcertissuer <- Func_splituple(VAL_Fieldsaltname)
	POSTCOND : VAL_Length > 0 && SIZE_Fieldsaltname = VAL_Length  && Func_endcheck(1) }

Authcertserial ::= Typecheck(130) Length Value(VAL_Length)
	{SIZE_Authcertserial <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Authcertserial <- Func_array_to_bytes_dsl(VAL_Value)
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length  && Func_endcheck(1) }

Fieldsextensionski(VAL_Extnid, VAL_Critical) ::= Subkeyid
	{SIZE_Fieldsextensionski <- SIZE_Subkeyid
	VAL_Critical <- Func_map_bool(VAL_Critical)
	VAL_Fieldsextensionski <- Func_Extn(VAL_Extnid, VAL_Critical , VAL_Subkeyid)
	POSTCOND : Func_endcheck(1) }

Subkeyid ::= Typecheck(4) Length Fieldssubkeyid
	{SIZE_Subkeyid <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldssubkeyid
	VAL_Subkeyid <- Func_Sub_key_id(VAL_Fieldssubkeyid)
	POSTCOND : VAL_Length > 0 && SIZE_Fieldssubkeyid = VAL_Length  && Func_endcheck(1) }

Fieldssubkeyid ::= Typecheck(4) Length Value(VAL_Length)
	{SIZE_Fieldssubkeyid <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Fieldssubkeyid <- Func_hex_n_bytes_to_int_dsl(VAL_Value)
	VAL_Fieldssubkeyid <- [VAL_Fieldssubkeyid, SIZE_Value]
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length  && Func_endcheck(1) }

Fieldsextensionsku(VAL_Extnid, VAL_Critical) ::= Keyusage
	{SIZE_Fieldsextensionsku <- SIZE_Keyusage
	VAL_Critical <- Func_map_bool(VAL_Critical)
	VAL_Fieldsextensionsku <- Func_Extn(VAL_Extnid, VAL_Critical , VAL_Keyusage)
	POSTCOND : Func_endcheck(1) }

Keyusage ::= Typecheck(4) Length Fieldskeyusage
	{SIZE_Keyusage <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldskeyusage
	VAL_Keyusage <- Func_Key_usage(VAL_Fieldskeyusage)
	POSTCOND : VAL_Length > 0 && SIZE_Fieldskeyusage = VAL_Length  && Func_endcheck(1) }

Fieldskeyusage ::= Typecheck(3) Length Kubitswithpadding(VAL_Length)
	{SIZE_Fieldskeyusage <- SIZE_Typecheck + SIZE_Length + SIZE_Kubitswithpadding
	VAL_Fieldskeyusage <- VAL_Kubitswithpadding
	POSTCOND : VAL_Length > 0 && SIZE_Kubitswithpadding = VAL_Length  && Func_endcheck(1) }

Kubitswithpadding(VAL_Length) ::= Padding Kubits(VAL_Length - 1)
	{SIZE_Kubitswithpadding <- SIZE_Padding + SIZE_Kubits
	VAL_Kubitswithpadding <- Func_array_to_bytes_dsl(VAL_Kubits)
	VAL_Kubitswithpadding <- Func_map_ku(VAL_Kubitswithpadding)
	PRECONDRET  : VAL_Length > 0
	POSTCOND : VAL_Padding <= Func_get_ku_padding_count_dsl(VAL_Kubits)}

Kubits(VAL_Length) ::= Bytee Kubits(VAL_Length - 1)
    { SIZE_Kubits <- SIZE_Bytee + SIZE_Kubits
    VAL_Kubits <- Func_addtotuple_dsl(VAL_Bytee, VAL_Kubits)
    PRECONDRET  : VAL_Length > 0}

Padding ::= RANGE(0, 7)
	{SIZE_Padding <- 1
	VAL_Padding <- Func_hex_n_bytes_to_int_dsl($1$)}

Fieldsextensionseku(VAL_Extnid, VAL_Critical) ::= Eku
	{SIZE_Fieldsextensionseku <- SIZE_Eku
	VAL_Critical <- Func_map_bool(VAL_Critical)
	VAL_Fieldsextensionseku <- Func_Extn(VAL_Extnid, VAL_Critical , VAL_Eku)
	POSTCOND :  Func_endcheck(1) }

Eku ::= Typecheck(4) Length Fieldseku
	{SIZE_Eku <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldseku
	VAL_Fieldseku <- Func_map_eku(VAL_Fieldseku)
	VAL_Eku <- Func_Ext_key_usage(VAL_Fieldseku)
	POSTCOND : VAL_Length > 0 && SIZE_Fieldseku = VAL_Length  && Func_endcheck(1) }

Fieldseku ::= Typecheck(48) Length Fieldsekuseq(VAL_Length)
	{SIZE_Fieldseku <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldsekuseq
	VAL_Fieldseku <- Func_splituple(VAL_Fieldsekuseq)
	POSTCOND : VAL_Length > 0 && SIZE_Fieldsekuseq = VAL_Length  && Func_endcheck(1) }

Fieldsekuseq(VAL_Length) ::= Keypurposeid Fieldsekuseq(VAL_Length - SIZE_Keypurposeid)
    { SIZE_Fieldsekuseq <- SIZE_Keypurposeid + SIZE_Fieldsekuseq
    VAL_Fieldsekuseq<- (VAL_Keypurposeid, VAL_Fieldsekuseq)
    PRECONDRET  : VAL_Length > 0}

Keypurposeid ::= Typecheck(6) Length Value(VAL_Length)
	{SIZE_Keypurposeid <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Keypurposeid <- Func_hex_n_bytes_to_int_dsl(VAL_Value)
	VAL_Keypurposeid <- [VAL_Keypurposeid, SIZE_Value]
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length  && Func_endcheck(1) }

Fieldsextensionsbc(VAL_Extnid, VAL_Critical) ::= Bc
	{SIZE_Fieldsextensionsbc <- SIZE_Bc
	VAL_Critical <- Func_map_bool(VAL_Critical)
	VAL_Fieldsextensionsbc <- Func_Extn(VAL_Extnid, VAL_Critical , VAL_Bc)
	POSTCOND :  Func_endcheck(1) }

Bc ::= Typecheck(4) Length Fieldsbc
	{SIZE_Bc <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldsbc
	VAL_Bc <- VAL_Fieldsbc
	POSTCOND : VAL_Length > 0 && SIZE_Fieldsbc = VAL_Length  && Func_endcheck(1) }

Fieldsbc ::= Typecheck(48) Length Fieldsbcseq
	{SIZE_Fieldsbc <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldsbcseq
	VAL_Fieldsbc <- VAL_Fieldsbcseq
	POSTCOND : SIZE_Fieldsbcseq = VAL_Length  && Func_endcheck(1) }

Fieldsbcseq ::= Ca_? Pathlen_?
	{SIZE_Fieldsbcseq <- SIZE_Ca + SIZE_Pathlen
	VAL_Ca <- Func_map_bool(VAL_Ca)
	VAL_Fieldsbcseq <- Func_Basic_constraints(VAL_Ca, VAL_Pathlen)
	POSTCOND : Func_endcheck(1) }

Fieldsextensionssan(VAL_Extnid, VAL_Critical) ::= San
	{SIZE_Fieldsextensionssan <- SIZE_San
	VAL_Critical <- Func_map_bool(VAL_Critical)
	VAL_Fieldsextensionssan <- Func_Extn(VAL_Extnid, VAL_Critical , VAL_San)
	POSTCOND :  Func_endcheck(1) }

San ::= Typecheck(4) Length Fieldssan
	{SIZE_San <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldssan
	VAL_San <- Func_Subject_alt_name(VAL_Fieldssan)
	POSTCOND : VAL_Length > 0 && SIZE_Fieldssan = VAL_Length  && Func_endcheck(1) }

Fieldssan ::= Typecheck(48) Length Fieldsaltname(VAL_Length)
	{SIZE_Fieldssan <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldsaltname
	VAL_Fieldssan <- Func_splituple(VAL_Fieldsaltname)
	POSTCOND : VAL_Length > 0 && SIZE_Fieldsaltname = VAL_Length  && Func_endcheck(1) }
	
Fieldsextensionsian(VAL_Extnid, VAL_Critical) ::= Ian
	{SIZE_Fieldsextensionsian <- SIZE_Ian
	VAL_Critical <- Func_map_bool(VAL_Critical)
	VAL_Fieldsextensionsian <- Func_Extn(VAL_Extnid, VAL_Critical , VAL_Ian)
	POSTCOND :  Func_endcheck(1) }

Ian ::= Typecheck(4) Length Fieldsian
	{SIZE_Ian <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldsian
	VAL_Ian <- Func_Issuer_alt_name(VAL_Fieldsian)
	POSTCOND : VAL_Length > 0 && SIZE_Fieldsian = VAL_Length  && Func_endcheck(1) }

Fieldsian ::= Typecheck(48) Length Fieldsaltname(VAL_Length)
	{SIZE_Fieldsian <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldsaltname
	VAL_Fieldsian <- Func_splituple(VAL_Fieldsaltname)
	POSTCOND : VAL_Length > 0 && SIZE_Fieldsaltname = VAL_Length  && Func_endcheck(1) }

Fieldsaltname(VAL_Length) ::= Generelname Fieldsaltname(VAL_Length - SIZE_Generelname)
    { SIZE_Fieldsaltname <- SIZE_Generelname + SIZE_Fieldsaltname
    VAL_Fieldsaltname <- (VAL_Generelname, VAL_Fieldsaltname)
    PRECONDRET  : VAL_Length > 0}

Generelname ::= Type Length Value(VAL_Length)
	{SIZE_Generelname <- SIZE_Type + SIZE_Length + SIZE_Value
	VAL_Value <- Func_array_to_bytes_dsl(VAL_Value)
	VAL_Generelname <- Func_GenerelName(VAL_Type, VAL_Value)
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length && Func_endcheck(1) }

Rdnsets(VAL_Length) ::= Rdnset Rdnsets(VAL_Length - SIZE_Rdnset)
    { SIZE_Rdnsets <- SIZE_Rdnset + SIZE_Rdnsets
    VAL_Rdnsets <- (VAL_Rdnset, VAL_Rdnsets)
    PRECONDRET  : VAL_Length > 0}

Rdnset ::= Typecheck(49) Length Rdnattrbtseq(VAL_Length)
	{SIZE_Rdnset <- SIZE_Typecheck + SIZE_Length + SIZE_Rdnattrbtseq
	VAL_Rdnset <- Func_splituple(VAL_Rdnattrbtseq)
	VAL_Rdnset <- Func_RDNset(VAL_Rdnset)
	POSTCOND : VAL_Length > 0 && SIZE_Rdnattrbtseq = VAL_Length  && Func_endcheck(1) }

Rdnattrbtseq(VAL_Length) ::= Rdnattrbt Rdnattrbtseq(VAL_Length - SIZE_Rdnattrbt)
    { SIZE_Rdnattrbtseq <- SIZE_Rdnattrbt + SIZE_Rdnattrbtseq
    VAL_Rdnattrbtseq <- (VAL_Rdnattrbt, VAL_Rdnattrbtseq)
    PRECONDRET  : VAL_Length > 0}

Rdnattrbt ::= Typecheck(48) Length Fieldsrdnattrbt
	{SIZE_Rdnattrbt <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldsrdnattrbt
	VAL_Rdnattrbt <- VAL_Fieldsrdnattrbt
	POSTCOND : VAL_Length > 0 && SIZE_Fieldsrdnattrbt = VAL_Length  && Func_endcheck(1) }

Fieldsrdnattrbt ::= Oid Stringvalue
	{SIZE_Fieldsrdnattrbt <- SIZE_Oid + SIZE_Stringvalue
	VAL_Fieldsrdnattrbt <- Func_Attribute(VAL_Oid, VAL_Stringvalue)
	POSTCOND :  Func_endcheck(1) }

Stringvalue ::= Type Length Value(VAL_Length)
	{SIZE_Stringvalue <- SIZE_Type + SIZE_Length + SIZE_Value
	VAL_Value <- Func_array_to_bytes_dsl(VAL_Value)
	VAL_Stringvalue <- Func_String(VAL_Type, VAL_Value)
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length && Func_endcheck(1) }

Oid ::= Typecheck(6) Length Value(VAL_Length)
	{SIZE_Oid <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Oid <- Func_hex_n_bytes_to_int_dsl(VAL_Value)
	VAL_Oid <- [VAL_Oid, SIZE_Value]
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length  && Func_endcheck(1) }

Certpolid ::= Typecheck(6) Length Value(VAL_Length)
	{SIZE_Certpolid <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Certpolid <- Func_hex_n_bytes_to_int_dsl(VAL_Value)
	VAL_Certpolid <- [VAL_Certpolid, SIZE_Value]
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length  && Func_endcheck(1) }

Policyquals(VAL_Lengthh) ::= Typecheck(48) Length Value(VAL_Length)
	{SIZE_Policyquals <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Policyquals <- Func_array_to_bytes_dsl(VAL_Value)
	PRECONDRET  : VAL_Lengthh > 0
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length  && Func_endcheck(1) }

Fieldspolicyinfo(VAL_Length) ::= Certpolid Policyquals(VAL_Length - SIZE_Certpolid)
    { SIZE_Fieldspolicyinfo <- SIZE_Certpolid + SIZE_Policyquals
    VAL_Fieldspolicyinfo <- Func_PolicyInformation(VAL_Certpolid, VAL_Policyquals)
    POSTCOND  : Func_endcheck(1)}

Policyinfo ::= Typecheck(48) Length Fieldspolicyinfo(VAL_Length)
	{SIZE_Policyinfo <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldspolicyinfo
	VAL_Policyinfo <- VAL_Fieldspolicyinfo
	POSTCOND : VAL_Length > 0 && SIZE_Fieldspolicyinfo = VAL_Length  && Func_endcheck(1) }

Policyinfos(VAL_Length) ::= Policyinfo Policyinfos(VAL_Length - SIZE_Policyinfo)
    { SIZE_Policyinfos <- SIZE_Policyinfo + SIZE_Policyinfos
    VAL_Policyinfos <- (VAL_Policyinfo, VAL_Policyinfos)
    PRECONDRET  : VAL_Length > 0}

Fieldsextensionscertpol(VAL_Extnid, VAL_Critical) ::= Certificatepolicy
	{SIZE_Fieldsextensionscertpol <- SIZE_Certificatepolicy
	VAL_Critical <- Func_map_bool(VAL_Critical)
	VAL_Fieldsextensionscertpol <- Func_Extn(VAL_Extnid, VAL_Critical , VAL_Certificatepolicy)
	POSTCOND : Func_endcheck(1) }

Certificatepolicy ::= Typecheck(4) Length Fieldscertificatepolicy
	{SIZE_Certificatepolicy <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldscertificatepolicy
	VAL_Certificatepolicy <- Func_Cert_policies(VAL_Fieldscertificatepolicy)
	POSTCOND : VAL_Length > 0 && SIZE_Fieldscertificatepolicy = VAL_Length  && Func_endcheck(1) }

Fieldscertificatepolicy ::= Typecheck(48) Length Policyinfos(VAL_Length)
	{SIZE_Fieldscertificatepolicy <- SIZE_Typecheck + SIZE_Length + SIZE_Policyinfos
	VAL_Fieldscertificatepolicy <- Func_splituple(VAL_Policyinfos)
	POSTCOND : VAL_Length > 0 && SIZE_Policyinfos = VAL_Length  && Func_endcheck(1) }

Fieldsextensionscrldist(VAL_Extnid, VAL_Critical) ::= Crldist
	{SIZE_Fieldsextensionscrldist <- SIZE_Crldist
	VAL_Critical <- Func_map_bool(VAL_Critical)
	VAL_Fieldsextensionscrldist <- Func_Extn(VAL_Extnid, VAL_Critical , VAL_Crldist)
	POSTCOND : Func_endcheck(1) }

Crldist ::= Typecheck(4) Length Fieldscrldist
	{SIZE_Crldist <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldscrldist
	VAL_Crldist <- Func_CRL_dist_points(VAL_Fieldscrldist)
	POSTCOND : VAL_Length > 0 && SIZE_Fieldscrldist = VAL_Length  && Func_endcheck(1) }

Fieldscrldist ::= Typecheck(48) Length Distributionpoints(VAL_Length)
	{SIZE_Fieldscrldist <- SIZE_Typecheck + SIZE_Length + SIZE_Distributionpoints
	VAL_Fieldscrldist <- Func_splituple(VAL_Distributionpoints)
	POSTCOND : VAL_Length > 0 && SIZE_Distributionpoints = VAL_Length  && Func_endcheck(1) }

Distributionpointname ::= Typecheck(160) Length Value(VAL_Length)
	{SIZE_Distributionpointname <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Distributionpointname <- Func_array_to_bytes_dsl(VAL_Value)
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length  && Func_endcheck(1) }

Reasons ::= Typecheck(129) Length Value(VAL_Length)
	{SIZE_Reasons <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Reasons <- Func_array_to_bytes_dsl(VAL_Value)
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length  && Func_endcheck(1) }

Crlissuer ::= Typecheck(162) Length Fieldsaltname(VAL_Length)
	{SIZE_Crlissuer <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldsaltname
	VAL_Crlissuer <- VAL_Fieldsaltname
	POSTCOND : VAL_Length > 0 && SIZE_Fieldsaltname = VAL_Length  && Func_endcheck(1) }

Fieldsdistributionpoint ::= Distributionpointname_? Reasons_? Crlissuer_?
	{SIZE_Fieldsdistributionpoint <- SIZE_Distributionpointname + SIZE_Reasons + SIZE_Crlissuer
	VAL_Fieldsdistributionpoint <- Func_DistributionPoint(VAL_Distributionpointname, VAL_Reasons , VAL_Crlissuer)
	POSTCOND : Func_endcheck(1) }

Distributionpoint ::= Typecheck(48) Length Fieldsdistributionpoint
	{SIZE_Distributionpoint <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldsdistributionpoint
	VAL_Distributionpoint <- VAL_Fieldsdistributionpoint
	POSTCOND : SIZE_Fieldsdistributionpoint = VAL_Length  && Func_endcheck(1) }

Distributionpoints(VAL_Length) ::= Distributionpoint Distributionpoints(VAL_Length - SIZE_Distributionpoint)
    { SIZE_Distributionpoints <- SIZE_Distributionpoint + SIZE_Distributionpoints
    VAL_Distributionpoints <- (VAL_Distributionpoint, VAL_Distributionpoints)
    PRECONDRET  : VAL_Length > 0}

Accesslocation ::= Type Length Value(VAL_Length)
	{SIZE_Accesslocation <- SIZE_Type + SIZE_Length + SIZE_Value
	VAL_Accesslocation <- Func_array_to_bytes_dsl(VAL_Value)
	VAL_Accesslocation <- Func_GenerelName(VAL_Type, VAL_Accesslocation)
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length && Func_endcheck(1) }

Accessmethod ::= Typecheck(6) Length Value(VAL_Length)
	{SIZE_Accessmethod <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Accessmethod <- Func_hex_n_bytes_to_int_dsl(VAL_Value)
	VAL_Accessmethod <- [VAL_Accessmethod, SIZE_Value]
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length  && Func_endcheck(1) }

Fieldsaccessdesc ::= Accessmethod Accesslocation
    { SIZE_Fieldsaccessdesc <- SIZE_Accessmethod + SIZE_Accesslocation
    VAL_Fieldsaccessdesc <- Func_AccessDescription(VAL_Accessmethod, VAL_Accesslocation)
    POSTCOND  : Func_endcheck(1)}

Accessdesc ::= Typecheck(48) Length Fieldsaccessdesc
	{SIZE_Accessdesc <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldsaccessdesc
	VAL_Accessdesc <- VAL_Fieldsaccessdesc
	POSTCOND : VAL_Length > 0 && SIZE_Fieldsaccessdesc = VAL_Length  && Func_endcheck(1) }

Fieldsaiaseq(VAL_Length) ::= Accessdesc Fieldsaiaseq(VAL_Length - SIZE_Accessdesc)
    { SIZE_Fieldsaiaseq <- SIZE_Accessdesc + SIZE_Fieldsaiaseq
    VAL_Fieldsaiaseq <- (VAL_Accessdesc, VAL_Fieldsaiaseq)
    PRECONDRET  : VAL_Length > 0}

Fieldsextensionsaia(VAL_Extnid, VAL_Critical) ::= Aia
	{SIZE_Fieldsextensionsaia <- SIZE_Aia
	VAL_Critical <- Func_map_bool(VAL_Critical)
	VAL_Fieldsextensionsaia <- Func_Extn(VAL_Extnid, VAL_Critical , VAL_Aia)
	POSTCOND : Func_endcheck(1) }

Aia ::= Typecheck(4) Length Fieldsaia
	{SIZE_Aia <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldsaia
	VAL_Aia <- Func_Authority_info_access(VAL_Fieldsaia)
	POSTCOND : VAL_Length > 0 && SIZE_Fieldsaia = VAL_Length  && Func_endcheck(1) }

Fieldsaia ::= Typecheck(48) Length Fieldsaiaseq(VAL_Length)
	{SIZE_Fieldsaia <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldsaiaseq
	VAL_Fieldsaia <- Func_splituple(VAL_Fieldsaiaseq)
	POSTCOND : VAL_Length > 0 && SIZE_Fieldsaiaseq = VAL_Length  && Func_endcheck(1) }

Notbefore ::= Type Length Fieldstime
	{SIZE_Notbefore <- SIZE_Type + SIZE_Length + SIZE_Fieldstime
	VAL_Notbefore <- Func_NotBefore(VAL_Fieldstime)
	POSTCOND : SIZE_Fieldstime = VAL_Length && ((VAL_Type = 23 && VAL_Length = 13) || (VAL_Type = 24 && VAL_Length = 15)) && Func_endcheck(1) }
	
Notafter ::= Type Length Fieldstime
	{SIZE_Notafter <- SIZE_Type + SIZE_Length + SIZE_Fieldstime
	VAL_Notafter <- Func_NotAfter(VAL_Fieldstime)
	POSTCOND : SIZE_Fieldstime = VAL_Length && ((VAL_Type = 23 && VAL_Length = 13) || (VAL_Type = 24 && VAL_Length = 15)) && Func_endcheck(1) }

Fieldstime ::=  Gentime
	{SIZE_Fieldstime <- SIZE_Gentime
	VAL_Fieldstime <- VAL_Gentime
	POSTCOND : Func_endcheck(1) }
	| Utctime
	{SIZE_Fieldstime <- SIZE_Utctime
	VAL_Fieldstime <- VAL_Utctime
	POSTCOND : Func_endcheck(1) }

Utctime ::= Yearone Yeartwo Monone Montwo Dayone Daytwo Hourone Hourtwo Minone Mintwo Secone Sectwo 90
	{SIZE_Utctime <- SIZE_Yearone + SIZE_Yeartwo + SIZE_Monone + SIZE_Montwo + SIZE_Dayone + SIZE_Daytwo + SIZE_Hourone + SIZE_Hourtwo + SIZE_Minone + SIZE_Mintwo + SIZE_Secone + SIZE_Sectwo + 1
	VAL_Year <- VAL_Yearone * 10 + VAL_Yeartwo
	VAL_Mon <- VAL_Monone * 10 + VAL_Montwo
	VAL_Day <- VAL_Dayone * 10 + VAL_Daytwo
	VAL_Hour <- VAL_Hourone * 10 + VAL_Hourtwo
	VAL_Min <- VAL_Minone * 10 + VAL_Mintwo
	VAL_Sec <- VAL_Secone * 10 + VAL_Sectwo
	VAL_Type <- 23
	VAL_Utctime <- [VAL_Year , VAL_Mon, VAL_Day , VAL_Hour , VAL_Min , VAL_Sec, VAL_Type]
	POSTCOND : 0 <= VAL_Year && VAL_Year <= 99 && 1 <= VAL_Mon && VAL_Mon <= 12 && 1 <= VAL_Day && VAL_Day <= 31 && 0 <= VAL_Hour && VAL_Hour <= 23 && 0 <= VAL_Min && VAL_Min <= 59 && 0 <= VAL_Sec && VAL_Sec <= 59 && Func_endcheck(1) }

Gentime ::= Yearone Yeartwo Yearthree Yearfour Monone Montwo Dayone Daytwo Hourone Hourtwo Minone Mintwo Secone Sectwo 90
	{SIZE_Gentime <- SIZE_Yearone + SIZE_Yeartwo + SIZE_Yearthree + SIZE_Yearfour + SIZE_Monone + SIZE_Montwo + SIZE_Dayone + SIZE_Daytwo + SIZE_Hourone + SIZE_Hourtwo + SIZE_Minone + SIZE_Mintwo + SIZE_Secone + SIZE_Sectwo + 1
	VAL_Year <- VAL_Yearone * 1000 + VAL_Yeartwo * 100 + VAL_Yearthree * 10 + VAL_Yearfour
	VAL_Mon <- VAL_Monone * 10 + VAL_Montwo
	VAL_Day <- VAL_Dayone * 10 + VAL_Daytwo
	VAL_Hour <- VAL_Hourone * 10 + VAL_Hourtwo
	VAL_Min <- VAL_Minone * 10 + VAL_Mintwo
	VAL_Sec <- VAL_Secone * 10 + VAL_Sectwo
	VAL_Type <- 24
	VAL_Gentime <- [VAL_Year , VAL_Mon, VAL_Day , VAL_Hour , VAL_Min , VAL_Sec, VAL_Type]
	POSTCOND : 0 <= VAL_Year && VAL_Year <= 9999 && 1 <= VAL_Mon && VAL_Mon <= 12 && 1 <= VAL_Day && VAL_Day <= 31 && 0 <= VAL_Hour && VAL_Hour <= 23 && 0 <= VAL_Min && VAL_Min <= 59 && 0 <= VAL_Sec && VAL_Sec <= 59 && Func_endcheck(1) }

Yearone ::= RANGE(48, 57)
	{SIZE_Yearone <- 1
	VAL_Yearone <- Func_hex_n_bytes_to_int_dsl($1$) - 48}

Yeartwo ::= RANGE(48, 57)
	{SIZE_Yeartwo <- 1
	VAL_Yeartwo <- Func_hex_n_bytes_to_int_dsl($1$) - 48}
	
Yearthree ::= RANGE(48, 57)
	{SIZE_Yearthree <- 1
	VAL_Yearthree <- Func_hex_n_bytes_to_int_dsl($1$) - 48}
	
Yearfour ::= RANGE(48, 57)
	{SIZE_Yearfour <- 1
	VAL_Yearfour <- Func_hex_n_bytes_to_int_dsl($1$) - 48}
	
Monone ::= RANGE(48, 57)
	{SIZE_Monone <- 1
	VAL_Monone <- Func_hex_n_bytes_to_int_dsl($1$) - 48}
	
Montwo ::= RANGE(48, 57)
	{SIZE_Montwo <- 1
	VAL_Montwo <- Func_hex_n_bytes_to_int_dsl($1$) - 48}
	
Dayone ::= RANGE(48, 57)
	{SIZE_Dayone <- 1
	VAL_Dayone <- Func_hex_n_bytes_to_int_dsl($1$) - 48}
	
Daytwo ::= RANGE(48, 57)
	{SIZE_Daytwo <- 1
	VAL_Daytwo <- Func_hex_n_bytes_to_int_dsl($1$) - 48}
	
Hourone ::= RANGE(48, 57)
	{SIZE_Hourone <- 1
	VAL_Hourone <- Func_hex_n_bytes_to_int_dsl($1$) - 48}
	
Hourtwo ::= RANGE(48, 57)
	{SIZE_Hourtwo <- 1
	VAL_Hourtwo <- Func_hex_n_bytes_to_int_dsl($1$) - 48}
	
Minone ::= RANGE(48, 57)
	{SIZE_Minone <- 1
	VAL_Minone <- Func_hex_n_bytes_to_int_dsl($1$) - 48}
	
Mintwo ::= RANGE(48, 57)
	{SIZE_Mintwo <- 1
	VAL_Mintwo <- Func_hex_n_bytes_to_int_dsl($1$) - 48}
	
Secone ::= RANGE(48, 57)
	{SIZE_Secone <- 1
	VAL_Secone <- Func_hex_n_bytes_to_int_dsl($1$) - 48}
	
Sectwo ::= RANGE(48, 57)
	{SIZE_Sectwo <- 1
	VAL_Sectwo <- Func_hex_n_bytes_to_int_dsl($1$) - 48}

Critical ::= Typecheck(1) Length Value(VAL_Length)
	{SIZE_Critical <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Critical <- Func_hex_n_bytes_to_int_dsl(VAL_Value)
	VAL_Critical <- VAL_Critical
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length  && Func_endcheck(1) }

Ca ::= Typecheck(1) Length Value(VAL_Length)
	{SIZE_Ca <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Ca <- Func_array_to_bytes_dsl(VAL_Value)
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length  && Func_endcheck(1) }

Pathlen ::= Typecheck(2) Length Value(VAL_Length)
	{SIZE_Pathlen <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Pathlen <- Func_hex_n_bytes_to_int_dsl(VAL_Value)
	VAL_Pathlen <- [VAL_Pathlen, SIZE_Value]
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length  && Func_endcheck(1) }

Fieldssignalgo(VAL_Length) ::= Signoid Signparam(VAL_Signoid, VAL_Length - SIZE_Signoid)
	{SIZE_Fieldssignalgo <- SIZE_Signoid + SIZE_Signparam
	VAL_Fieldssignalgo <- Func_AlgorithmIdentifier(VAL_Signoid , VAL_Signparam )
	POSTCOND : Func_endcheck(1) }

Fieldssignalgopk(VAL_Length) ::= Signoid Signparampk(VAL_Signoid, VAL_Length - SIZE_Signoid)
	{SIZE_Fieldssignalgopk <- SIZE_Signoid + SIZE_Signparampk
	VAL_Fieldssignalgopk <- Func_AlgorithmIdentifier(VAL_Signoid , VAL_Signparampk )
	POSTCOND : Func_endcheck(1) }