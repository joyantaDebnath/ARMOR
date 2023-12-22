open import Armor.Binary
open import Armor.Data.X690-DER.Time.TimeType.TCB
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Prelude

module Armor.Data.X690-DER.Time.Day.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8

Day : @0 List UInt8 → Set
Day = TimeType 2 1 31

RawDay : Raw Day
RawDay = RawTimeType _ _ _
