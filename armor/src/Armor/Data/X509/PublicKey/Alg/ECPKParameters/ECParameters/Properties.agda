open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.TCB
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Properties where

open Armor.Grammar.Definitions              UInt8
open Armor.Grammar.Option                   UInt8
open Armor.Grammar.Seq                      UInt8

iso : Iso ECParametersFieldsRep ECParametersFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ (─ refl) (mk&ₚ fieldID (mk&ₚ curve (mk&ₚ base (mk&ₚ order cofactor refl) refl) refl) refl) refl) =
  refl
proj₂ (proj₂ iso) (mkECParametersFields self fieldID curve base order cofactor refl) =
  refl

@0 unambiguousFields : Unambiguous ECParametersFields
unambiguousFields =
  Iso.unambiguous iso
    (Seq.unambiguous (erased-unique ≡-unique) (λ where _ (─ refl) (─ refl) → refl)
    (Seq.unambiguous FieldID.unambiguous TLV.nosubstrings
    (Seq.unambiguous Curve.unambiguous TLV.nosubstrings
    (Seq.unambiguous OctetString.unambiguous TLV.nosubstrings
    (Seq.unambiguous Int.unambiguous TLV.nosubstrings
                     (Option.unambiguous Int.unambiguous TLV.nonempty))))))

@0 unambiguous : Unambiguous ECParameters
unambiguous = TLV.unambiguous unambiguousFields

@0 nonmalleableFields : NonMalleable RawECParametersFields
nonmalleableFields =
  Iso.nonmalleable iso RawECParametersFieldsRep
    (Seq.nonmalleable (subsingleton⇒nonmalleable (λ where (─ _ , ─ refl) (─ _ , ─ refl) → refl))
    (Seq.nonmalleable{ra = RawFieldID} FieldID.nonmalleable
    (Seq.nonmalleable{ra = RawCurve} Curve.nonmalleable
    (Seq.nonmalleable{ra = RawOctetString} OctetString.nonmalleable
    (Seq.nonmalleable{ra = RawInt}{rb = RawOption RawInt}
       Int.nonmalleable (Option.nonmalleable _ Int.nonmalleable))))))

@0 nonmalleable : NonMalleable RawECParameters
nonmalleable = TLV.nonmalleable nonmalleableFields

instance
  eq≋ : Eq≋ ECParametersFields
  eq≋ =
    Iso.isoEq≋ iso
      (Seq.eq≋&ₚ (record { _≋?_ = λ where (─ refl) (─ refl) → yes ≋-refl })
      (Seq.eq≋&ₚ it
      (Seq.eq≋&ₚ it
      (Seq.eq≋&ₚ it
      (Seq.eq≋&ₚ it it)))))
