open import Armor.Binary.Bits.TCB
open import Armor.Binary.UInt6
open import Armor.Binary.UInt8.TCB
open import Armor.Prelude

module Armor.Binary.Base64EncDec.Base64 where

charset : List Char
charset = String.toList "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

∈charsetUnique : ∀ {c} → (c∈₁ c∈₂ : c ∈ charset) → c∈₁ ≡ c∈₂
∈charsetUnique = ∈-unique (toWitness{Q = List.unique? _≟_ charset} tt)

isByteRep : ∀ c → Dec (c ∈ charset)
isByteRep c = Any.any? (c ≟_) charset

toUInt6 : Char → Maybe UInt6
toUInt6 c
  with isByteRep c
... | no  c∉charset = nothing
... | yes c∈charset = just (Any.index c∈charset)

toByte : Char → Maybe (Binary 6)
toByte c = do
  d ← toUInt6 c
  return (toBinary d)

isPad : ∀ c → Dec (c ≡ '=')
isPad = _≟ '='

data Pad : Set where
  pad2 : Vec (Binary 6) 2 → Pad
  pad1 : Vec (Binary 6) 3 → Pad
