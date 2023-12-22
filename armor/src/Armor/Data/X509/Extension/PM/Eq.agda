open import Armor.Binary
open import Armor.Data.X509.Extension.PM.Properties
open import Armor.Data.X509.Extension.PM.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.SequenceOf.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.PM.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ PolicyMapFields
  eq≋ = Iso.isoEq≋ iso (Seq.eq≋&ₚ it it)
