open import Armor.Binary
open import Armor.Data.X509.Extension.PC.Properties
open import Armor.Data.X509.Extension.PC.TCB
open import Armor.Data.X690-DER.Int
import      Armor.Data.X690-DER.OctetString.Properties
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.PC.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ PCFieldsSeqFields
  eq≋ = Iso.isoEq≋ iso (Seq.eq≋&ₚ it it)
