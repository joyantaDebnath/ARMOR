open import Armor.Binary
open import Armor.Data.X509.Extension.AKI.TCB
open import Armor.Data.X509.GeneralNames
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq

open import Armor.Prelude

module Armor.Data.X509.Extension.AKI.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

iso : Iso AKIFieldsSeqFieldsRep AKIFieldsSeqFields
proj₁ iso = equivalentAKIFieldsSeqFields
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) = refl
proj₂ (proj₂ iso) (mkAKIFieldsSeqFields akeyid authcertiss authcertsn refl) = refl

@0 unambiguous : Unambiguous AKIFields
unambiguous =
  TLV.unambiguous (TLV.unambiguous (Iso.unambiguous iso
    (Seq.unambiguous₂Option₃
      (TLV.unambiguous OctetString.unambiguousValue) TLV.nosubstrings TLV.nonempty
      (TLV.unambiguous GeneralNames.GeneralNamesElems.unambiguous) TLV.nosubstrings TLV.nonempty
      Int.[ _ ]unambiguous TLV.nonempty
      (TLV.noconfusion (λ ())) (TLV.noconfusion λ ()) (TLV.noconfusion λ ()))))

@0 nonmalleable : NonMalleable RawAKIFields
nonmalleable = TLV.nonmalleable (TLV.nonmalleable
                 (Iso.nonmalleable iso RawAKIFieldsSeqFieldsRep nm))
  where
  nm : NonMalleable RawAKIFieldsSeqFieldsRep
  nm = Seq.nonmalleable (Option.nonmalleable _ (TLV.nonmalleable OctetString.nonmalleableValue))
      (Seq.nonmalleable (Option.nonmalleable _ (TLV.nonmalleable GeneralNames.GeneralNamesElems.nonmalleable))
                        (Option.nonmalleable _ Int.[ _ ]nonmalleable))
