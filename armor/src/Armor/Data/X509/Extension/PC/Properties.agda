open import Armor.Binary
open import Armor.Data.X509.Extension.PC.TCB
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.PC.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

iso : Iso PCFieldsSeqFieldsRep PCFieldsSeqFields
proj₁ iso = equivalentPCFieldsSeqFields
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ refl) = refl
proj₂ (proj₂ iso) (mkPCFieldsSeqFields require inhibit refl) = refl

@0 unambiguous : Unambiguous PCFields
unambiguous = TLV.unambiguous (TLV.unambiguous
  (Iso.unambiguous iso
    (Seq.unambiguousOption₂
      Int.[ _ ]unambiguous TLV.nosubstrings TLV.nonempty
      Int.[ _ ]unambiguous TLV.nonempty
      (TLV.noconfusion λ ()))))

@0 nonmalleable : NonMalleable RawPCFields
nonmalleable = TLV.nonmalleable (TLV.nonmalleable
  (Iso.nonmalleable iso
    RawPCFieldsSeqFieldsRep
    (Seq.nonmalleable (Option.nonmalleable _ Int.[ _ ]nonmalleable)
      (Option.nonmalleable _ Int.[ _ ]nonmalleable))))
