open import Armor.Binary
open import Armor.Data.X509.Extension.BC.Properties
open import Armor.Data.X509.Extension.BC.TCB
open import Armor.Data.X690-DER.Boool
open import Armor.Data.X690-DER.Default
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.BC.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ BCFieldsSeqFields
  eq≋ = Iso.isoEq≋ iso (Seq.eq≋&ₚ (Default.eq≋ falseBoool) it)
