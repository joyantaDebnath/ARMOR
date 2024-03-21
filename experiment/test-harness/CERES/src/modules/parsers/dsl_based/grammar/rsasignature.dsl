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

Pkcs ::= 0 Bt Padding Pkcsseq
    { SIZE_Pkcs <- 1 + SIZE_Bt + SIZE_Padding + SIZE_Pkcsseq
    VAL_Pkcs <- VAL_Pkcsseq
    POSTCOND  : SIZE_Padding >= 9 && Func_endcheck(2)}

Bt ::= 1
    { SIZE_Bt <- 1
    VAL_Bt <- 1
    POSTCOND  : Func_endcheck(1)}

Padding ::= 255 Padding
    { SIZE_Padding <- 1 + SIZE_Padding
    VAL_Padding <- Func_addtotuple_dsl(255, VAL_Padding)
    POSTCOND  : Func_endcheck(1)}
    | 0
	{ SIZE_Padding <- 1
    VAL_Padding <- 0
    POSTCOND  : Func_endcheck(1)}

Pkcsseq ::= Typecheck(48) Length Signalgo Digest
	{SIZE_Pkcsseq <- SIZE_Typecheck + SIZE_Length + SIZE_Signalgo + SIZE_Digest
	VAL_Pkcsseq <- Func_addtotuple_dsl(VAL_Signalgo, VAL_Digest)
	POSTCOND : VAL_Length > 0 && SIZE_Signalgo + SIZE_Digest = VAL_Length  && Func_endcheck(2) }

Digest ::= Typecheck(4) Length Value(VAL_Length)
	{SIZE_Digest <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Digest <- Func_array_to_bytes_dsl(VAL_Value)
	POSTCOND : VAL_Length > 0 && SIZE_Value = VAL_Length  && Func_endcheck(2) }

Signalgo ::= Typecheck(48) Length Fieldssignalgo(VAL_Length)
	{SIZE_Signalgo <- SIZE_Typecheck + SIZE_Length + SIZE_Fieldssignalgo
	VAL_Signalgo <- VAL_Fieldssignalgo
	POSTCOND : VAL_Length > 0 && SIZE_Fieldssignalgo = VAL_Length  && Func_endcheck(1) }

Fieldssignalgo(VAL_Length) ::= Signoid Signparam(VAL_Length - SIZE_Signoid)
	{SIZE_Fieldssignalgo <- SIZE_Signoid + SIZE_Signparam
	VAL_Fieldssignalgo <- Func_AlgorithmIdentifier(VAL_Signoid , VAL_Signparam )
	POSTCOND : Func_endcheck(1) }

Signoid ::= Typecheck(6) Length Value(VAL_Length)
	{SIZE_Signoid <- SIZE_Typecheck + SIZE_Length + SIZE_Value
	VAL_Signoid <- Func_hex_n_bytes_to_int_dsl(VAL_Value)
	VAL_Signoid <- [VAL_Signoid, SIZE_Value]
	POSTCOND : SIZE_Value = VAL_Length  && Func_endcheck(1) }

Signparam(VAL_Lenthh) ::= Type Length Value(VAL_Length)
	{SIZE_Signparam <- SIZE_Type + SIZE_Length + SIZE_Value
	VAL_Value <- Func_array_to_bytes_dsl(VAL_Value)
	VAL_Signparam <- Func_Parameter(VAL_Type, VAL_Value)
	PRECONDRET : VAL_Lenthh > 0
	POSTCOND : SIZE_Value = VAL_Length && (VAL_Type = 5 && VAL_Length = 0) && Func_endcheck(1) }