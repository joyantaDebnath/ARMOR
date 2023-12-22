open import Armor.Binary
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.IList
open import Armor.Prelude

module Armor.Data.X690-DER.Strings.VisibleString.TCB where

open Armor.Grammar.IList UInt8
open Armor.Grammar.Definitions.NonMalleable UInt8

record VisibleStringValue (@0 bs : List UInt8) : Set where
  constructor mkVisibleStringValue
  field
    chars : List UInt8
    @0 range : All (InRange 32 127) chars
    @0 bs≡ : bs ≡ chars

  size : ℕ
  size = length chars

VisibleString = TLV Tag.VisibleString VisibleStringValue

RawVisibleStringValue : Raw VisibleStringValue
Raw.D RawVisibleStringValue = List UInt8
Raw.to RawVisibleStringValue = VisibleStringValue.chars

RawVisibleString : Raw VisibleString 
RawVisibleString = RawTLV _ RawVisibleStringValue
