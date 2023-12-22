open import Armor.Binary
open import Armor.Data.X509.Validity.Time.TCB
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.Time.GeneralizedTime
open import Armor.Data.X690-DER.Time.UTCTime
import      Armor.Grammar.Sum
import      Armor.Grammar.Definitions
open import Armor.Prelude

module Armor.Data.X509.Validity.Time.Properties where

open Armor.Grammar.Sum         UInt8
open Armor.Grammar.Definitions UInt8

iso : Iso TimeRep Time
proj₁ iso = equivalent
proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
proj₁ (proj₂ iso) (Sum.inj₂ x) = refl
proj₂ (proj₂ iso) (generalized x) = refl
proj₂ (proj₂ iso) (utc x) = refl

@0 nosubstrings : NoSubstrings Time
nosubstrings =
  Iso.nosubstrings equivalent
    (Sum.nosubstrings
      TLV.nosubstrings
      TLV.nosubstrings
      (TLV.noconfusion λ ()))

@0 unambiguous : Unambiguous Time
unambiguous =
  Iso.unambiguous iso
    (Sum.unambiguous GeneralizedTime.unambiguous UTCTime.unambiguous
      (TLV.noconfusion λ ()))

@0 nonmalleable : NonMalleable RawTime
nonmalleable =
  Iso.nonmalleable iso RawTimeRep
    (Sum.nonmalleable GeneralizedTime.nonmalleable UTCTime.nonmalleable)

instance
  eq : Eq (Exists─ (List UInt8) Time)
  eq = Iso.isoEq iso (Sum.sumEq ⦃ it ⦄ ⦃ it ⦄)
