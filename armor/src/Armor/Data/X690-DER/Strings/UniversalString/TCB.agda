open import Armor.Binary
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Data.Unicode.UTF32.TCB
open import Armor.Prelude

module Armor.Data.X690-DER.Strings.UniversalString.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8

UniversalString : @0 List UInt8 → Set
UniversalString = TLV Tag.UniversalString UTF32

RawUniversalString : Raw UniversalString 
RawUniversalString = RawTLV _ RawUTF32
