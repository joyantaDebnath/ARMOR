open import Armor.Binary
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.Time.GeneralizedTime.TCB
open import Armor.Data.X690-DER.Time.MDHMS
open import Armor.Data.X690-DER.Time.TimeType
open import Armor.Data.X690-DER.Time.Year
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X690-DER.Time.GeneralizedTime.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Seq         UInt8

@0 nosubstrings : NoSubstrings GeneralizedTimeFields
nosubstrings = Iso.nosubstrings equivalent
  (Seq.nosubstrings (Seq.nosubstrings TimeType.nosubstrings MDHMS.nosubstrings)
  (λ where _ (─ refl) (─ refl) → refl))

iso : Iso GeneralizedTimeFieldsRep GeneralizedTimeFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ (mk&ₚ{y}{m} year mdhms refl) (─ refl) refl) =
  subst₀ (λ eq → _≡_{A = GeneralizedTimeFieldsRep _}
                   (mk&ₚ (mk&ₚ year mdhms refl) (─ refl) eq)
                   (mk&ₚ (mk&ₚ year mdhms refl) (─ refl) refl))
         (sym (trans-symʳ (++-assoc y m [ # 'Z' ]))) refl
proj₂ (proj₂ iso) (mkGeneralizedTime{y}{m} year mdhms refl) =
  subst₀
    (λ eq → _≡_{A = GeneralizedTimeFields _}
             (mkGeneralizedTime year mdhms eq)
             (mkGeneralizedTime year mdhms refl))
    (sym (trans-symˡ (++-assoc y m [ # 'Z' ]))) refl

@0 unambiguousFields : Unambiguous GeneralizedTimeFields
unambiguousFields =
  Iso.unambiguous iso
    (Seq.unambiguous
      (Seq.unambiguous TimeType.unambiguous TimeType.nosubstrings MDHMS.unambiguous)
      (Seq.nosubstrings TimeType.nosubstrings MDHMS.nosubstrings)
      (erased-unique ≡-unique))

@0 unambiguous : Unambiguous GeneralizedTime
unambiguous = TLV.unambiguous unambiguousFields

@0 nonmalleableFields : NonMalleable RawGeneralizedTimeFields
nonmalleableFields =
  Iso.nonmalleable iso RawGeneralizedTimeFieldsRep nm
  where
  nm : NonMalleable RawGeneralizedTimeFieldsRep
  nm =
    Seq.nonmalleable
      (Seq.nonmalleable TimeType.nonmalleable MDHMS.nonmalleable)
      (subsingleton⇒nonmalleable (λ where (─ _ , ─ refl) (─ _ , ─ refl) → refl))

@0 nonmalleable : NonMalleable RawGeneralizedTime
nonmalleable = TLV.nonmalleable nonmalleableFields

instance
  eq : Eq (Exists─ (List UInt8) GeneralizedTimeFields)
  eq = Iso.isoEq iso (Seq.eq&ₚ (Seq.eq&ₚ it it) (record { _≟_ = λ where (─ _ , ─ refl) (─ _ , ─ refl) → yes refl }))
