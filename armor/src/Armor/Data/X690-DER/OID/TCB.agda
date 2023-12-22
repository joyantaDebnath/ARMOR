open import Armor.Binary
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.SequenceOf.TCB
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Prelude

module Armor.Data.X690-DER.OID.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8

-- https://www.itu.int/rec/T-REC-X.690-202102-I/en
-- 8.19.1 The encoding of an object identifier value shall be primitive.
-- 8.19.2 The contents octets shall be an (ordered) list of encodings of subidentifiers (see 8.19.3 and 8.19.4) concatenated
-- together.
-- Each subidentifier is represented as a series of (one or more) octets. Bit 8 of each octet indicates whether it is the last in the
-- series: bit 8 of the last octet is zero; bit 8 of each preceding octet is one. Bits 7 to 1 of the octets in the series collectively
-- encode the subidentifier. Conceptually, these groups of bits are concatenated to form an unsigned binary number whose most
-- significant bit is bit 7 of the first octet and whose least significant bit is bit 1 of the last octet. The subidentifier shall be
-- encoded in the fewest possible octets, that is, the leading octet of the subidentifier shall not have the value 8016.
-- 8.19.3 The number of subidentifiers (N) shall be one less than the number of object identifier components in the object
-- identifier value being encoded.
-- 8.19.4 The numerical value of the first subidentifier is derived from the values of the first two object identifier components
-- in the object identifier value being encoded, using the formula:
-- (X*40) + Y
-- where X is the value of the first object identifier component and Y is the value of the second object identifier component.
-- NOTE – This packing of the first two object identifier components recognizes that only three values are allocated from the root node,
-- and at most 39 subsequent values from nodes reached by X = 0 and X = 1.
-- 8.19.5 The numerical value of the ith subidentifier, (2  i  N) is that of the (i + 1)th object identifier component.

LeastBytes : List UInt8 → Set
LeastBytes = maybe (Fin._> # 128) ⊤ ∘ head

leastBytes? : Decidable LeastBytes
leastBytes? [] = yes tt
leastBytes? (b ∷ bs) = (# 128) Fin.<? b

leastBytesUnique : ∀ {bs} → Unique (LeastBytes bs)
leastBytesUnique{[]} tt tt = refl
leastBytesUnique{b ∷ bs} x₁ x₂ = ≤-irrelevant x₁ x₂
  where open import Data.Nat.Properties

record OIDSub (@0 bs : List UInt8) : Set where
  constructor mkOIDSub
  field
    lₚ : List UInt8
    @0 lₚ≥128 : All (λ d → toℕ d ≥ 128) lₚ
    lₑ   : UInt8
    @0 lₑ<128 : toℕ lₑ < 128
    @0 leastDigs : LeastBytes lₚ
    @0 bs≡ : bs ≡ lₚ ∷ʳ lₑ

-- TODO: sharpen this
RawOIDSub : Raw OIDSub
Raw.D RawOIDSub = List UInt8
Raw.to RawOIDSub (mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 leastDigs bs≡) = lₚ ∷ʳ lₑ

OIDValue : @0 List UInt8 → Set
OIDValue = NonEmptySequenceOf OIDSub

RawOIDValue : Raw OIDValue
RawOIDValue = RawBoundedSequenceOf RawOIDSub 1

OID : @0 List UInt8 → Set
OID = TLV Tag.ObjectIdentifier OIDValue

RawOID : Raw OID
RawOID = RawTLV _ RawOIDValue
