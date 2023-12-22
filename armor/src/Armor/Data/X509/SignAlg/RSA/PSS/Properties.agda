-- open import Armor.Binary
-- open import Armor.Data.X509.HashAlg
-- import      Armor.Data.X509.HashAlg.TCB.OIDs        as OIDs
-- open import Armor.Data.X509.MaskGenAlg
-- open import Armor.Data.X509.SignAlg.RSA.PSS.TCB
-- import      Armor.Data.X509.SignAlg.TCB.OIDs        as OIDs
-- open import Armor.Data.X690-DER.Int
-- open import Armor.Data.X690-DER.OID.TCB
-- open import Armor.Data.X690-DER.OctetString.TCB
-- open import Armor.Data.X690-DER.Sequence.DefinedByOID
-- open import Armor.Data.X690-DER.TLV
-- import      Armor.Data.X690-DER.Tag                 as Tag
-- import      Armor.Grammar.Definitions
-- import      Armor.Grammar.Option
-- import      Armor.Grammar.Parallel
-- import      Armor.Grammar.Properties
-- import      Armor.Grammar.Seq
-- import      Armor.Grammar.Sum
-- open import Armor.Prelude

module Armor.Data.X509.SignAlg.RSA.PSS.Properties where

-- open Armor.Grammar.Definitions UInt8
-- open Armor.Grammar.Option      UInt8
-- open Armor.Grammar.Parallel    UInt8
-- open Armor.Grammar.Properties  UInt8
-- open Armor.Grammar.Seq         UInt8
-- open Armor.Grammar.Sum         UInt8

-- iso : Iso PSSParamFieldsRep PSSParamFields
-- proj₁ iso = equivalent
-- proj₁ (proj₂ iso) (mk&ₚ hashAlg (mk&ₚ maskGenAlg (mk&ₚ saltLen trailerField refl) refl) refl) = refl
-- proj₂ (proj₂ iso) (mkPSSParam hashAlg maskGenAlg saltLength trailerField refl) = refl

-- @0 unambiguous : Unambiguous PSSParamSeq
-- unambiguous =
--   TLV.unambiguous
--     (Iso.unambiguous iso
--       (Seq.unambiguous{A = PSSHashAlg}
--         (TLV.unambiguous
--           (Option.unambiguous HashAlg.RFC4055.unambiguous TLV.nonempty))
--         TLV.nosubstrings
--       (Seq.unambiguous
--         (TLV.unambiguous
--           (Option.unambiguous MaskGenAlg.RFC4055.unambiguous TLV.nonempty))
--         TLV.nosubstrings
--       (Seq.unambiguous
--         (TLV.unambiguous (Option.unambiguous Int.unambiguous TLV.nonempty))
--         TLV.nosubstrings
--           (TLV.unambiguous
--             (Option.unambiguous
--               (Parallel.unambiguous Int.unambiguous (λ _ → ≡-unique))
--               (Parallel.nonempty₁ TLV.nonempty)))))))

-- @0 nonmalleable : NonMalleable RawPSSParamSeq
-- nonmalleable =
--   TLV.nonmalleable {R = RawPSSParamFields}
--     (Iso.nonmalleable iso RawPSSParamFieldsRep
--       (Seq.nonmalleable{ra = RawTLV _ (RawOption HashAlg.RawHashAlg)} {!!} {!!}))

-- module Fields where
--   module SupportedHashAlg where
--     @0 noConfusion-SHA1-
--       : NoConfusion
--           HashAlg.SHA1
--           (Sum HashAlg.SHA224
--           (Sum HashAlg.SHA256
--           (Sum HashAlg.SHA384
--                HashAlg.SHA512)))
--     noConfusion-SHA1- =
--       (Sum.noconfusion {A = HashAlg.SHA1} (HashAlg.SHA-Like.noConfusion _ _)
--         (Sum.noconfusion {A = HashAlg.SHA1} (HashAlg.SHA-Like.noConfusion _ _)
--           (Sum.noconfusion {A = HashAlg.SHA1} (HashAlg.SHA-Like.noConfusion _ _) (HashAlg.SHA-Like.noConfusion _ _))))

--     @0 noConfusion-SHA224-
--       : NoConfusion HashAlg.SHA224
--           (Sum HashAlg.SHA256 (Sum HashAlg.SHA384 HashAlg.SHA512))
--     noConfusion-SHA224- =
--       Sum.noconfusion {A = HashAlg.SHA224} (HashAlg.SHA-Like.noConfusion _ _)
--        (Sum.noconfusion{A = HashAlg.SHA224}
--          (HashAlg.SHA-Like.noConfusion _ _) (HashAlg.SHA-Like.noConfusion _ _))

--     @0 noConfusion-SHA256-
--       : NoConfusion HashAlg.SHA256 (Sum HashAlg.SHA384 HashAlg.SHA512)
--     noConfusion-SHA256- =
--       Sum.noconfusion{A = HashAlg.SHA256}
--        (HashAlg.SHA-Like.noConfusion _ _)
--        (HashAlg.SHA-Like.noConfusion _ _)

--     @0 unambiguous : Unambiguous SupportedHashAlg
--     unambiguous =
--       Sum.unambiguous (HashAlg.SHA-Like.unambiguous _)
--         (Sum.unambiguous (HashAlg.SHA-Like.unambiguous _)
--           (Sum.unambiguous (HashAlg.SHA-Like.unambiguous _)
--             (Sum.unambiguous
--               (HashAlg.SHA-Like.unambiguous _)
--               (HashAlg.SHA-Like.unambiguous _)
--               (HashAlg.SHA-Like.noConfusion _ _))
--             noConfusion-SHA256-)
--           noConfusion-SHA224-)
--         noConfusion-SHA1-

--     @0 nosubstrings : NoSubstrings SupportedHashAlg
--     nosubstrings =
--       Sum.nosubstrings TLV.nosubstrings
--         (Sum.nosubstrings TLV.nosubstrings
--           (Sum.nosubstrings TLV.nosubstrings
--             (Sum.nosubstrings TLV.nosubstrings TLV.nosubstrings
--               (HashAlg.SHA-Like.noConfusion _ _))
--             noConfusion-SHA256-)
--           noConfusion-SHA224-)
--         noConfusion-SHA1-

--     nonempty : NonEmpty SupportedHashAlg
--     nonempty = TLV.nonempty ∘ SH.erase

--   Rep : @0 List UInt8 → Set
--   Rep =  &ₚ (TLV Tag.AA0 (Option SupportedHashAlg))
--         (&ₚ (TLV Tag.AA1 (Option MGF1.MaskGenAlg))
--         (&ₚ (TLV Tag.AA2 (Option Int))
--             (TLV Tag.AA3 (Option (Σₚ Int λ _ i → Int.getVal i ≡ ℤ.1ℤ)))))

--   equiv : Equivalent Rep PSSParamFields
--   proj₁ equiv (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ (mk&ₚ fstₚ₃ sndₚ₁ refl) refl) bs≡) =
--     mkPSSParam fstₚ₁ fstₚ₂ fstₚ₃ sndₚ₁ bs≡
--   proj₂ equiv (mkPSSParam hashAlg maskGenAlgo saltLength trailerField bs≡) =
--     mk&ₚ hashAlg (mk&ₚ maskGenAlgo (mk&ₚ saltLength trailerField refl) refl) bs≡

--   iso   : Iso Rep PSSParamFields
--   proj₁ iso = equiv
--   proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ (mk&ₚ fstₚ₃ sndₚ₁ refl) refl) bs≡) = refl
--   proj₂ (proj₂ iso) (mkPSSParam hashAlg maskGenAlgo saltLength trailerField bs≡) = refl

--   @0 unambiguous : Unambiguous PSSParamFields
--   unambiguous =
--     Iso.unambiguous iso
--       (Seq.unambiguous
--         (TLV.unambiguous
--           (Option.unambiguous SupportedHashAlg.unambiguous SupportedHashAlg.nonempty))
--         TLV.nosubstrings
--         (Seq.unambiguous
--           (TLV.unambiguous
--             (Option.unambiguous MGF1.unambiguous TLV.nonempty))
--           TLV.nosubstrings
--           (Seq.unambiguous
--             (TLV.unambiguous (Option.unambiguous Int.unambiguous
--               TLV.nonempty))
--             TLV.nosubstrings
--             (TLV.unambiguous
--               (Option.unambiguous
--                 (Parallel.unambiguous Int.unambiguous
--                   (λ _ → ≡-unique))
--                 (Parallel.nonempty₁ TLV.nonempty))))))

-- @0 unambiguous : Unambiguous PSS
-- unambiguous =
--   TLV.unambiguous
--     (DefinedByOID.unambiguous PSSParam
--       λ o →
--        Parallel.unambiguous×ₚ Fields.unambiguous
--          (λ where
--            ≋-refl ≋-refl → refl))

