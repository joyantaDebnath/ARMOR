open import Armor.Binary
open import Armor.Data.X690-DER.Strings.UTF8String.TCB
import      Armor.Data.X690-DER.TLV.Properties as TLV
import      Armor.Data.Unicode.UTF8.Properties as UTF8
import      Armor.Grammar.Definitions.NonMalleable.Base
open import Armor.Prelude

module Armor.Data.X690-DER.Strings.UTF8String.Properties where

open Armor.Grammar.Definitions.NonMalleable.Base UInt8

@0 nonmalleable : NonMalleable RawUTF8String
nonmalleable = TLV.nonmalleable UTF8.nonmalleable
