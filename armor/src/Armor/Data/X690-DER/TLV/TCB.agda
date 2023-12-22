open import Armor.Binary
open import Armor.Data.X690-DER.Length.TCB
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Prelude

module Armor.Data.X690-DER.TLV.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8
  using (Raw)

-- https://www.itu.int/rec/T-REC-X.690-202102-I/en
-- 8.1.1.1 The encoding of a data value shall consist of four components which shall appear in the following order:
-- a) identifier octets (see 8.1.2);
-- b) length octets (see 8.1.3);
-- c) contents octets (see 8.1.4);

record TLV (t : UInt8) (A : @0 List UInt8 → Set) (@0 bs : List UInt8) : Set where
  constructor mkTLV
  field
    @0 {l v} : List UInt8
    len : Length l
    val : A v
    @0 len≡ : getLength len ≡ length v
    @0 bs≡  : bs ≡ t ∷ l ++ v

TLVNonEmptyVal : ∀ {t}{A : @0 List UInt8 → Set} → (@0 bs : List UInt8) (tlv : TLV t A bs) → Set
TLVNonEmptyVal bs tlv = 1 ≤ getLength (TLV.len tlv)

TLVLenBounded : ∀ {t}{A : @0 List UInt8 → Set} → (l u : ℕ) → (@0 bs : List UInt8) (tlv : TLV t A bs) → Set
TLVLenBounded l u bs tlv = InRange l u (getLength (TLV.len tlv))

TLVSizeBounded : ∀ {t} {A : @0 List UInt8 → Set} (len : ∀ {@0 bs} → A bs → ℕ) (l u : ℕ) → ∀ (@0 bs) → TLV t A bs → Set
TLVSizeBounded len l u bs tlv = InRange l u (len (TLV.val tlv))

RawTLV : ∀ t {A} → Raw A → Raw (TLV t A)
Raw.D (RawTLV t R) = Raw.D R
Raw.to (RawTLV t R) tlv = Raw.to R (TLV.val tlv)
