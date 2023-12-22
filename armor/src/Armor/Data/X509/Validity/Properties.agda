open import Armor.Binary
open import Armor.Data.X509.Validity.TCB
open import Armor.Data.X509.Validity.Time
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.Time
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Validity.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Seq         UInt8

iso : Iso ValidityFieldsRep ValidityFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkValidityFields start end bs≡) = refl

@0 nosubstrings : NoSubstrings ValidityFields
nosubstrings =
  Iso.nosubstrings equivalent
    (Seq.nosubstrings Time.nosubstrings Time.nosubstrings)

@0 unambiguousFields : Unambiguous ValidityFields
unambiguousFields = Iso.unambiguous iso (Seq.unambiguous Time.unambiguous Time.nosubstrings Time.unambiguous)

@0 unambiguous : Unambiguous Validity
unambiguous = TLV.unambiguous unambiguousFields

@0 nonmalleableFields : NonMalleable RawValidityFields
nonmalleableFields =
  Iso.nonmalleable iso RawValidityFieldsRep
    (Seq.nonmalleable Time.nonmalleable Time.nonmalleable)

@0 nonmalleable : NonMalleable RawValidity
nonmalleable = TLV.nonmalleable nonmalleableFields

instance
  eq : Eq (Exists─ (List UInt8) ValidityFields)
  eq = Iso.isoEq iso (Seq.eq&ₚ it it)

  eq≋ : Eq≋ ValidityFields
  eq≋ = Eq⇒Eq≋ it

-- instance
--   EqValidity : Eq (Exists─ (List UInt8) ValidityFields)
--   EqValidity = Iso.isoEq iso (Seq.eq&ₚ it it)

--   eq≋ : Eq≋ ValidityFields
--   eq≋ = Eq⇒Eq≋ it
