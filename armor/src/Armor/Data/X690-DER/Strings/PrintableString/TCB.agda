open import Armor.Binary
open import Armor.Data.X690-DER.Strings.PrintableString.Char.TCB
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.IList.TCB
open import Armor.Prelude

module Armor.Data.X690-DER.Strings.PrintableString.TCB where

open Armor.Grammar.IList.TCB UInt8
open Armor.Grammar.Definitions.NonMalleable UInt8

PrintableString : @0 List UInt8 → Set
PrintableString = TLV Tag.PrintableString (IList PrintableStringChar)

size : ∀ {@0 bs} → IList PrintableStringChar bs → ℕ
size = lengthIList

RawPrintableStringValue : Raw (IList PrintableStringChar)
Raw.D RawPrintableStringValue = List UInt8
Raw.to RawPrintableStringValue = Raw.to (RawIList RawPrintableStringChar)

RawPrintableString : Raw PrintableString 
RawPrintableString = RawTLV _ RawPrintableStringValue
