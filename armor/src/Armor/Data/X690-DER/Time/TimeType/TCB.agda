open import Armor.Arith
open import Armor.Binary
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Prelude

module Armor.Data.X690-DER.Time.TimeType.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8

record TimeType (@0 size l u : ℕ) (@0 bs : List UInt8) : Set where
  constructor mkTimeType
  field
    @0 charset : True (All.all? (inRange? '0' '9') bs)
    time : Singleton (asciiNum bs)
    @0 bsLen : length bs ≡ size
    @0 range : InRange l u time

  getTime : ℕ
  getTime = ↑ time

RawTimeType : (size l u : ℕ) → Raw (TimeType size l u)
Raw.D (RawTimeType size l u) = ℕ
Raw.to (RawTimeType size l u) = ↑_ ∘ TimeType.time

encodeℕ : (size n : ℕ) → List UInt8
encodeℕ size n = showFixed size (n mod10^n size)
