open import Armor.Binary
open import Armor.Data.Unicode.UTF8.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.NonMalleable.Base
open import Armor.Prelude

module Armor.Data.X690-DER.Strings.UTF8String.TCB where

open Armor.Grammar.Definitions.NonMalleable.Base UInt8

UTF8String : @0 List UInt8 → Set
UTF8String = TLV Tag.UTF8String UTF8

RawUTF8String : Raw UTF8String 
RawUTF8String = RawTLV _ RawUTF8
