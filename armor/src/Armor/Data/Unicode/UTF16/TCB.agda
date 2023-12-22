open import Armor.Binary
import      Armor.Grammar.IList.TCB
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Prelude

module Armor.Data.Unicode.UTF16.TCB where

-- We only support the BMP restriction of UTF16

open Armor.Grammar.Definitions.NonMalleable UInt8
open Armor.Grammar.IList.TCB UInt8

record BMPChar (@0 bs : List UInt8) : Set where
  constructor mkBMPChar
  field
    c₁ c₂ : UInt8
    @0 range : InRange 0 215 c₁ ⊎ InRange 224 255 c₁
    @0 bs≡ : bs ≡ c₁ ∷ [ c₂ ]

RawBMPChar : Raw BMPChar
Raw.D RawBMPChar = Vec UInt8 2
Raw.to RawBMPChar y = (BMPChar.c₁ y) ∷ (BMPChar.c₂ y) ∷ []

BMP : @0 List UInt8 → Set
BMP = IList BMPChar

RawBMP : Raw BMP
RawBMP = RawIList RawBMPChar

size : ∀ {@0 bs} → BMP bs → ℕ
size bmp = lengthIList bmp
