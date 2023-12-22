open import Armor.Binary
open import Armor.Data.X690-DER.Time.TimeType.TCB
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Prelude

module Armor.Data.X690-DER.Time.Hour.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8

Hour : @0 List UInt8 → Set
Hour = TimeType 2 0 23

RawHour : Raw Hour
RawHour = RawTimeType _ _ _
