open import Armor.Binary
open import Armor.Data.X690-DER.Strings.UniversalString.TCB
import      Armor.Data.X690-DER.TLV.Properties as TLV
import      Armor.Data.Unicode.UTF32.Properties as UTF32
import      Armor.Grammar.Definitions.NonMalleable.Base
open import Armor.Prelude

module Armor.Data.X690-DER.Strings.UniversalString.Properties where

open Armor.Grammar.Definitions.NonMalleable.Base UInt8

@0 nonmalleable : NonMalleable RawUniversalString
nonmalleable = TLV.nonmalleable UTF32.nonmalleable
