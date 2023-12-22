open import Armor.Binary
open import Armor.Data.X690-DER.Time.TimeType.TCB
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Prelude

module Armor.Data.X690-DER.Time.Sec.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8

Sec : @0 List UInt8 → Set
Sec = TimeType 2 0 60

RawSec : Raw Sec
RawSec = RawTimeType _ _ _
