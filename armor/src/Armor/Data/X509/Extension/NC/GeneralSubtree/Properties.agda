open import Armor.Binary
open import Armor.Data.X509.Extension.NC.GeneralSubtree.TCB
open import Armor.Data.X509.GeneralNames.GeneralName
open import Armor.Data.X690-DER.Default
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.Sequence
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.NC.GeneralSubtree.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

iso : Iso GeneralSubtreeFieldsRep GeneralSubtreeFields
proj₁ iso = equivalentGeneralSubtreeFields
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) = refl
proj₂ (proj₂ iso) (mkGeneralSubtreeFields base minimum maximum refl) = refl

@0 unambiguousFields : Unambiguous GeneralSubtreeFields
unambiguousFields =
  Iso.unambiguous iso
    (Seq.unambiguous GeneralName.unambiguous GeneralName.nosubstrings
      (Sequence.unambiguousDefaultOption _
        Int.[ _ ]unambiguous TLV.nosubstrings TLV.nonempty
        Int.[ _ ]unambiguous TLV.nonempty
        (TLV.noconfusion λ ())))

@0 unambiguous : Unambiguous GeneralSubtrees
unambiguous =
  SequenceOf.Bounded.unambiguous (TLV.unambiguous unambiguousFields)
    TLV.nonempty TLV.nosubstrings

@0 nonmalleable : NonMalleable RawGeneralSubtrees
nonmalleable = SequenceOf.Bounded.nonmalleable TLV.nonempty TLV.nosubstrings
  (TLV.nonmalleable
    (Iso.nonmalleable iso RawGeneralSubtreeFieldsRep
      (Seq.nonmalleable GeneralName.nonmalleable
        (Seq.nonmalleable (Default.nonmalleable defaultMinBaseDistance
            (TLV.nonmalleable Int.nonmalleableVal))
          (Option.nonmalleable _ (TLV.nonmalleable Int.nonmalleableVal))))))
