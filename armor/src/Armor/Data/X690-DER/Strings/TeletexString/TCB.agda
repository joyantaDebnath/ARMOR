open import Armor.Binary
open import Armor.Data.X690-DER.OctetString.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Data.X690-DER.TLV.TCB
open import Armor.Prelude

module Armor.Data.X690-DER.Strings.TeletexString.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8

TeletexString : @0 List UInt8 → Set
TeletexString = TLV Tag.TeletexString OctetStringValue

RawTeletexString : Raw TeletexString 
RawTeletexString = RawTLV _ RawOctetStringValue
