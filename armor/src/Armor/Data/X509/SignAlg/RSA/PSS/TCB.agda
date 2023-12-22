-- open import Armor.Binary
-- import      Armor.Data.X509.HashAlg.RFC4055.TCB     as RFC4055
-- import      Armor.Data.X509.HashAlg.TCB.OIDs        as OIDs
-- import      Armor.Data.X509.MaskGenAlg.RFC4055.TCB  as RFC4055
-- import      Armor.Data.X509.SignAlg.TCB.OIDs        as OIDs
-- open import Armor.Data.X690-DER.Int.TCB
-- open import Armor.Data.X690-DER.OID.TCB
-- open import Armor.Data.X690-DER.OctetString.TCB
-- open import Armor.Data.X690-DER.Sequence.DefinedByOID
-- open import Armor.Data.X690-DER.TLV.TCB
-- import      Armor.Data.X690-DER.Tag                 as Tag
-- import      Armor.Grammar.Definitions
-- import      Armor.Grammar.Option.TCB
-- import      Armor.Grammar.Parallel.TCB
-- import      Armor.Grammar.Seq.TCB
-- import      Armor.Grammar.Sum.TCB
-- open import Armor.Prelude

module Armor.Data.X509.SignAlg.RSA.PSS.TCB where

-- open Armor.Grammar.Definitions  UInt8
-- open Armor.Grammar.Option.TCB   UInt8
-- open Armor.Grammar.Parallel.TCB UInt8
-- open Armor.Grammar.Seq.TCB      UInt8
-- open Armor.Grammar.Sum.TCB      UInt8

-- SupportedHashAlg : @0 List UInt8 → Set
-- SupportedHashAlg =
--    Sum HashAlg.SHA1
--   (Sum HashAlg.SHA224
--   (Sum HashAlg.SHA256
--   (Sum HashAlg.SHA384
--        HashAlg.SHA512)))

-- module SupportedHashAlg where
--   erase : ∀ {@0 bs} → SupportedHashAlg bs → DefinedByOID (λ _ bs → Erased (OctetStringValue bs)) bs
--   erase (inj₁ (mkTLV len (mkOIDDefinedFields o p refl) len≡ bs≡)) =
--     mkTLV len (mkOIDDefinedFields o (─ self) refl) len≡ bs≡
--   erase (inj₂ (inj₁ (mkTLV len (mkOIDDefinedFields o p refl) len≡ bs≡))) =
--     mkTLV len (mkOIDDefinedFields o (─ self) refl) len≡ bs≡
--   erase (inj₂ (inj₂ (inj₁ (mkTLV len (mkOIDDefinedFields o p refl) len≡ bs≡)))) =
--     mkTLV len (mkOIDDefinedFields o (─ self) refl) len≡ bs≡
--   erase (inj₂ (inj₂ (inj₂ (inj₁ (mkTLV len (mkOIDDefinedFields o p refl) len≡ bs≡))))) =
--     mkTLV len (mkOIDDefinedFields o (─ self) refl) len≡ bs≡
--   erase (inj₂ (inj₂ (inj₂ (inj₂ (mkTLV len (mkOIDDefinedFields o p refl) len≡ bs≡))))) =
--     mkTLV len (mkOIDDefinedFields o (─ self) refl) len≡ bs≡

--   {- https://datatracker.ietf.org/doc/html/rfc4055#section-3.1 -}
{-
      id-RSASSA-PSS  OBJECT IDENTIFIER  ::=  { pkcs-1 10 }

      RSASSA-PSS-params  ::=  SEQUENCE  {
         hashAlgorithm      [0] HashAlgorithm DEFAULT
                                   sha1Identifier,
         maskGenAlgorithm   [1] MaskGenAlgorithm DEFAULT
                                   mgf1SHA1Identifier,
         saltLength         [2] INTEGER DEFAULT 20,
         trailerField       [3] INTEGER DEFAULT 1  }
-}
-- PSSHashAlg PSSMaskGenAlg PSSSaltLen PSSTrailer : @0 List UInt8 → Set

-- PSSHashAlg    = TLV Tag.AA0 (Option RFC4055.HashAlg)
-- PSSMaskGenAlg = TLV Tag.AA1 (Option RFC4055.MGF1)
-- PSSSaltLen    = TLV Tag.AA2 (Option Int)
-- PSSTrailer    = TLV Tag.AA3 (Option (Σₚ Int (λ _ i → getVal i ≡ ℤ.1ℤ)))

-- record PSSParamFields (@0 bs : List UInt8) : Set where
--   constructor mkPSSParam
--   field
--     @0 {h m s t} : List UInt8
-- -- hashAlgorithm

-- --    The hashAlgorithm field identifies the hash function.  It MUST
-- --    be one of the algorithm identifiers listed in Section 2.1, and
-- --    the default hash function is SHA-1.  Implementations MUST
-- --    support SHA-1 and MAY support any of the other one-way hash
-- --    functions listed in Section 2.1.  Implementations that perform
-- --    signature generation MUST omit the hashAlgorithm field when
-- --    SHA-1 is used, indicating that the default algorithm was used.
-- --    Implementations that perform signature validation MUST
-- --    recognize both the sha1Identifier algorithm identifier and an
-- --    absent hashAlgorithm field as an indication that SHA-1 was
-- --    used.
--     hashAlg : PSSHashAlg h

-- -- maskGenAlgorithm

-- --    The maskGenAlgorithm field identifies the mask generation
-- --    function.  The default mask generation function is MGF1 with
-- --    SHA-1.  For MGF1, it is strongly RECOMMENDED that the
-- --    underlying hash function be the same as the one identified by
-- --    hashAlgorithm.  Implementations MUST support MGF1.  MGF1
-- --    requires a one-way hash function that is identified in the
-- --    parameters field of the MGF1 algorithm identifier.
-- --    Implementations MUST support SHA-1 and MAY support any of the
-- --    other one-way hash functions listed in section Section 2.1.
-- --    The MGF1 algorithm identifier is comprised of the id-mgf1
-- --    object identifier and a parameter that contains the algorithm
-- --    identifier of the one-way hash function employed with MGF1.
-- --    The SHA-1 algorithm identifier is comprised of the id-sha1
-- --    object identifier and an (optional) parameter of NULL.
-- --    Implementations that perform signature generation MUST omit the
-- --    maskGenAlgorithm field when MGF1 with SHA-1 is used, indicating
-- --    that the default algorithm was used.

-- --    Although mfg1SHA1Identifier is defined as the default value for
-- --    this field, implementations MUST accept both the default value
-- --    encoding (i.e., an absent field) and mfg1SHA1Identifier to be
-- --    explicitly present in the encoding.
--     maskGenAlg : PSSMaskGenAlg m

-- -- saltLength

-- --    The saltLength field is the octet length of the salt.  For a
-- --    given hashAlgorithm, the recommended value of saltLength is the
-- --    number of octets in the hash value.  Unlike the other fields of
-- --    type RSASSA-PSS-params, saltLength does not need to be fixed
-- --    for a given RSA key pair; a different value could be used for
-- --    each RSASSA-PSS signature generated.
--     saltLength : PSSSaltLen s

-- -- trailerField

-- --    The trailerField field is an integer.  It provides
-- --    compatibility with IEEE Std 1363a-2004 [P1363A].  The value
-- --    MUST be 1, which represents the trailer field with hexadecimal
-- --    value 0xBC.  Other trailer fields, including the trailer field
-- --    composed of HashID concatenated with 0xCC that is specified in
-- --    IEEE Std 1363a, are not supported.  Implementations that
-- --    perform signature generation MUST omit the trailerField field,
-- --    indicating that the default trailer field value was used.
-- --    Implementations that perform signature validation MUST
-- --    recognize both a present trailerField field with value 1 and an
-- --    absent trailerField field.
--     trailerField : PSSTrailer t

--     @0 bs≡ : bs ≡ h ++ m ++ s ++ t

-- PSSParamFieldsRep : @0 List UInt8 → Set
-- PSSParamFieldsRep =
--    &ₚ PSSHashAlg
--   (&ₚ PSSMaskGenAlg
--   (&ₚ PSSSaltLen
--       PSSTrailer))

-- equivalent : Equivalent PSSParamFieldsRep PSSParamFields
-- proj₁ equivalent (mk&ₚ hash (mk&ₚ mask (mk&ₚ salt trail refl) refl) refl) =
--   mkPSSParam hash mask salt trail refl
-- proj₂ equivalent (mkPSSParam hashAlg maskGenAlg saltLength trailerField refl) =
--   mk&ₚ hashAlg (mk&ₚ maskGenAlg (mk&ₚ saltLength trailerField refl) refl) refl

-- RawPSSParamFieldsRep : Raw PSSParamFieldsRep
-- RawPSSParamFieldsRep =
--    Raw&ₚ (RawTLV _ (RawOption RFC4055.RawHashAlg))
--   (Raw&ₚ (RawTLV _ (RawOption RFC4055.RawMGF1))
--   (Raw&ₚ (RawTLV _ (RawOption RawInt))
--          (RawTLV _ (RawOption (RawΣₚ₁ RawInt _)))))

-- RawPSSParamFields : Raw PSSParamFields
-- RawPSSParamFields = Iso.raw equivalent RawPSSParamFieldsRep

-- PSSParamSeq : @0 List UInt8 → Set
-- PSSParamSeq = TLV Tag.Sequence PSSParamFields

-- RawPSSParamSeq : Raw PSSParamSeq
-- RawPSSParamSeq = RawTLV _ RawPSSParamFields
