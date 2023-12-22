open import Armor.Binary
open import Armor.Data.X690-DER.Time.TimeType.TCB
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Prelude

module Armor.Data.X690-DER.Time.Minute.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8

Minute : @0 List UInt8 → Set
Minute = TimeType 2 0 59

RawMinute : Raw Minute
RawMinute = RawTimeType _ _ _
