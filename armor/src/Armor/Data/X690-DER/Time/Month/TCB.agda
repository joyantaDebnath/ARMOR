open import Armor.Binary
open import Armor.Data.X690-DER.Time.TimeType.TCB
import      Armor.Grammar.Definitions.NonMalleable.Base
open import Armor.Prelude

module Armor.Data.X690-DER.Time.Month.TCB where

open Armor.Grammar.Definitions.NonMalleable.Base UInt8

Month : @0 List UInt8 → Set
Month = TimeType 2 1 12

-- ISO 8601 3.1 (Table 1)
daysInMonth : ∀ {@0 bs} → Month bs → ℕ
daysInMonth m =
  let month = TimeType.getTime m in
  if ⌊ month ∈? 1 ∷ 3 ∷ 5 ∷ 7 ∷ 8 ∷ 10 ∷ [ 12 ] ⌋ then 31
  else if ⌊ month ≟ 2 ⌋ then 29
  else 30

RawMonth : Raw Month
RawMonth = RawTimeType _ _ _
