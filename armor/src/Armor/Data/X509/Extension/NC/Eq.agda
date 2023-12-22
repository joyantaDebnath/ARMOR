open import Armor.Binary
open import Armor.Data.X509.Extension.NC.GeneralSubtree
open import Armor.Data.X509.Extension.NC.Properties
open import Armor.Data.X509.Extension.NC.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.SequenceOf
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.NC.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ NCFieldsSeqFields
  eq≋ = Iso.isoEq≋ iso (Seq.eq≋&ₚ it it)
    where
    instance
      e : Eq≋ (NonEmptySequenceOf GeneralSubtree)
      e = SequenceOf.BoundedSequenceOfEq≋ ⦃ it ⦄
