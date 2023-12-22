open import Armor.Binary
open import Armor.Data.X690-DER.Length.TCB
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Prelude

module Armor.Data.X690-DER.Boool.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8
  using (Raw)

-- https://www.itu.int/rec/T-REC-X.690-202102-I/en
-- 8.2.1 The encoding of a boolean value shall be primitive. The contents octets shall consist of a single octet.
-- 8.2.2 If the boolean value is:
-- FALSE
-- the octet shall be zero.
-- If the boolean value is
-- TRUE
-- the octet shall have any non-zero value, as a sender's option.
-- If the encoding represents the boolean value TRUE, its single contents octet shall have all eight bits set to one. (Contrast with
-- 8.2.2.)

data BoolRep : Bool → UInt8 → Set where
  falseᵣ : BoolRep false (# 0)
  trueᵣ  : BoolRep true (# 255)

record BoolValue (@0 bs : List UInt8) : Set where
  constructor mkBoolValue
  field
    v     : Bool
    @0 b  : UInt8
    @0 vᵣ : BoolRep v b
    @0 bs≡ : bs ≡ [ b ]

Boool = TLV Tag.Boolean BoolValue

RawBoolValue : Raw BoolValue
Raw.D RawBoolValue = Bool
Raw.to RawBoolValue = BoolValue.v

RawBoool : Raw Boool
RawBoool = RawTLV Tag.Boolean RawBoolValue

falseBoool : Boool _
falseBoool = mkTLV (short (mkShort (# 1) (s≤s (s≤s z≤n)) refl)) (mkBoolValue _ _ falseᵣ refl) refl refl

trueBoool : Boool _
trueBoool = mkTLV (short (mkShort (# 1) (s≤s (s≤s z≤n)) refl)) (mkBoolValue  _ _ trueᵣ refl) refl refl
