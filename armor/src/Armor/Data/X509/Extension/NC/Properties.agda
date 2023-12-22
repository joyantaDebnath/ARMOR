open import Armor.Binary
open import Armor.Data.X509.Extension.NC.GeneralSubtree
open import Armor.Data.X509.Extension.NC.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.SequenceOf
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.NC.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

iso : Iso NCFieldsSeqFieldsRep NCFieldsSeqFields
proj₁ iso = equivalentNCFieldsSeqFields
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ refl) = refl
proj₂ (proj₂ iso) (mkNCFieldsSeqFields permt excld refl) = refl

@0 unambiguous : Unambiguous NCFields
unambiguous = TLV.unambiguous  (TLV.unambiguous
  (Iso.unambiguous iso
    (Seq.unambiguousOption₂
      (TLV.unambiguous GeneralSubtree.unambiguous)
        TLV.nosubstrings TLV.nonempty
       (TLV.unambiguous  GeneralSubtree.unambiguous)
       TLV.nonempty (TLV.noconfusion (λ ()))))) 

@0 nonmalleable : NonMalleable RawNCFields
nonmalleable = TLV.nonmalleable (TLV.nonmalleable
                 (Iso.nonmalleable iso RawNCFieldsSeqFieldsRep
                 (Seq.nonmalleable (Option.nonmalleable _ (TLV.nonmalleable GeneralSubtree.nonmalleable))
                                   (Option.nonmalleable _ (TLV.nonmalleable GeneralSubtree.nonmalleable)))))
