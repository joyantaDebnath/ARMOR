open import Armor.Binary
open import Armor.Data.X690-DER.SequenceOf.TCB
open import Armor.Data.X690-DER.SetOf.Order.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.IList.TCB
import      Armor.Grammar.Parallel.TCB
open import Armor.Prelude
  hiding (length)
import      Data.List.Relation.Unary.Sorted.TotalOrder

module Armor.Data.X690-DER.SetOf.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8
open Armor.Grammar.IList.TCB                UInt8
open Armor.Grammar.Parallel.TCB             UInt8

-- https://www.itu.int/rec/T-REC-X.690-202102-I/en
-- 8.12.1 The encoding of a set-of value shall be constructed.
-- 8.12.2 The text of 8.10.2 applies.
-- 8.12.3 The order of data values need not be preserved by the encoding and subsequent decoding.

-- 11.6 Set-of components
-- The encodings of the component values of a set-of value shall appear in ascending order, the encodings being compared as
-- octet strings with the shorter components being padded at their trailing end with 0-octets.
-- NOTE – The padding octets are for comparison purposes only and do not appear in the encodings.

record SetOfFields (A : @0 List UInt8 → Set) (@0 bs : List UInt8) : Set where
  constructor mkSetOfFields
  field
    elems : NonEmptySequenceOf A bs

  open Data.List.Relation.Unary.Sorted.TotalOrder bytesTotalOrder
  @0 orderingList : List (List UInt8)
  orderingList = liftMapErase{A = Exists─ _ A} proj₁ (toList (fstₚ elems))

  field
    @0 order : True (sorted? _≲?_ orderingList)

  toSequenceOf : SequenceOf A bs
  toSequenceOf = fstₚ elems

  length : ℕ
  length = lengthSequence toSequenceOf

SetOf : (A : @0 List UInt8 → Set) → @0 List UInt8 → Set
SetOf A = TLV Tag.Sett (SetOfFields A)

RawSetOfFields : {A : @0 List UInt8 → Set} → Raw A → Raw (SetOfFields A)
Raw.D (RawSetOfFields R) = Raw.D (RawBoundedSequenceOf R 1)
Raw.to (RawSetOfFields R) so = Raw.to (RawBoundedSequenceOf R 1) (SetOfFields.elems so)

RawSetOf : {A : @0 List UInt8 → Set} → Raw A → Raw (SetOf A)
RawSetOf R = RawTLV _ (RawSetOfFields R)
