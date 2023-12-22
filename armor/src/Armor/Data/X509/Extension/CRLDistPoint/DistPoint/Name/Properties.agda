open import Armor.Binary
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name.TCB
open import Armor.Data.X509.GeneralNames
open import Armor.Data.X509.Name
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Sum
open import Armor.Prelude

module Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Sum         UInt8

nosubstrings : NoSubstrings DistPointNameChoice
nosubstrings x (fullname x₁) (fullname x₂) = ‼ TLV.nosubstrings x x₁ x₂
nosubstrings x (fullname x₁) (nameRTCrlissr x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (nameRTCrlissr x₁) (fullname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (nameRTCrlissr x₁) (nameRTCrlissr x₂) = ‼ TLV.nosubstrings x x₁ x₂

iso : Iso DistPointNameChoiceRep DistPointNameChoice
proj₁ iso = equivalentDistPointNameChoice
proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
proj₁ (proj₂ iso) (Sum.inj₂ x) = refl
proj₂ (proj₂ iso) (fullname x) = refl
proj₂ (proj₂ iso) (nameRTCrlissr x) = refl

@0 unambiguous : Unambiguous DistPointName
unambiguous =
  TLV.unambiguous (Iso.unambiguous iso
    (Sum.unambiguous (TLV.unambiguous GeneralNames.GeneralNamesElems.unambiguous)
                     Name.RDN.[ Tag.AA1 ]unambiguous (TLV.noconfusion λ ())))

@0 nonmalleable : NonMalleable RawDistPointName
nonmalleable = TLV.nonmalleable (Iso.nonmalleable iso RawDistPointNameChoiceRep nm)
  where
  nm : NonMalleable RawDistPointNameChoiceRep
  nm = Sum.nonmalleable{ra = RawTLV _ RawGeneralNamesElems}{rb = Name.[ Tag.AA1 ]RawRDN}
         (TLV.nonmalleable GeneralNames.GeneralNamesElems.nonmalleable)
         Name.RDN.[ Tag.AA1 ]nonmalleable
