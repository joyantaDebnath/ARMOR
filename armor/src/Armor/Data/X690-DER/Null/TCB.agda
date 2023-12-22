open import Armor.Binary
import      Armor.Data.X690-DER.Length.Properties as Length
open import Armor.Data.X690-DER.Length.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Prelude

module Armor.Data.X690-DER.Null.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8

-- https://www.itu.int/rec/T-REC-X.690-202102-I/en
-- 8.8.1 The encoding of a null value shall be primitive.
-- 8.8.2 The contents octets shall not contain any octets.
-- NOTE – The length octet is zero.

Null = TLV Tag.Null (λ x → Erased (x ≡ []))

nullTLV : Null (Tag.Null ∷ [ # 0 ])
nullTLV = mkTLV (Length.shortₛ (# 0)) (─ refl) refl refl

RawNull : Raw Null
RawNull = RawTLV _ RawSubSingleton
