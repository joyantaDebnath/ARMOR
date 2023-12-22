open import Armor.Binary
import      Armor.Grammar.IList.TCB
import      Armor.Grammar.Definitions.Iso
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.Sum.TCB
open import Armor.Prelude

module Armor.Data.Unicode.UTF8.TCB where

open Armor.Grammar.Definitions.Iso          UInt8
open Armor.Grammar.Definitions.NonMalleable UInt8
open Armor.Grammar.IList.TCB                UInt8
open Armor.Grammar.Sum.TCB                  UInt8

record UTF8Char1 (@0 bs : List UInt8) : Set where
  constructor mkUTF8Char1
  field
    b₁ : UInt8
    @0 b₁range : toℕ b₁ < 128
    @0 bs≡ : bs ≡ [ b₁ ]

RawUTF8Char1 : Raw UTF8Char1
Raw.D RawUTF8Char1 = Vec UInt8 1
Raw.to RawUTF8Char1 x = Vec.[ UTF8Char1.b₁ x ]

record UTF8Char2 (@0 bs : List UInt8) : Set where
  constructor mkUTF8Char2
  field
    b₁ b₂ : UInt8
    @0 b₁range : InRange 192 223 b₁
    @0 b₂range : InRange 128 191 b₂
    @0 bs≡ : bs ≡ b₁ ∷ [ b₂ ]

InRangeUTF8Char2 : (l₁ u₁ l₂ u₂ : UInt8) → ∀ {@0 bs} → UTF8Char2 bs → Set
InRangeUTF8Char2 l₁ u₁ l₂ u₂ x = InRange l₁ u₁ b₁ × InRange l₂ u₂ b₂
  where open UTF8Char2 x

RawUTF8Char2 : Raw UTF8Char2
Raw.D RawUTF8Char2 = Vec UInt8 2
Raw.to RawUTF8Char2 x = UTF8Char2.b₁ x ∷ Vec.[ UTF8Char2.b₂ x ]

record UTF8Char3 (@0 bs : List UInt8) : Set where
  constructor mkUTF8Char3
  field
    b₁ b₂ b₃ : UInt8
    @0 b₁range : InRange 224 239 b₁
    @0 b₂range : InRange 128 191 b₂
    @0 b₃range : InRange 128 191 b₃

    @0 bs≡ : bs ≡ b₁ ∷ b₂ ∷ [ b₃ ]

InRangeUTF8Char3 : (l₁ u₁ l₂ u₂ l₃ u₃ : UInt8) → ∀ {@0 bs} → UTF8Char3 bs → Set
InRangeUTF8Char3 l₁ u₁ l₂ u₂ l₃ u₃ x = InRange l₁ u₁ b₁ × InRange l₂ u₂ b₂ × InRange l₃ u₃ b₃
  where open UTF8Char3 x

RawUTF8Char3 : Raw UTF8Char3
Raw.D RawUTF8Char3 = Vec UInt8 3
Raw.to RawUTF8Char3 x = UTF8Char3.b₁ x ∷ UTF8Char3.b₂ x ∷ Vec.[ UTF8Char3.b₃ x ]

record UTF8Char4 (@0 bs : List UInt8) : Set where
  constructor mkUTF8Char4
  field
    b₁ b₂ b₃ b₄ : UInt8
    @0 b₁range : InRange 240 247 b₁
    @0 b₂range : InRange 128 191 b₂
    @0 b₃range : InRange 128 191 b₃
    @0 b₄range : InRange 128 191 b₄
    @0 bs≡ : bs ≡ b₁ ∷ b₂ ∷ b₃ ∷ [ b₄ ]

InRangeUTF8Char4 : (l₁ u₁ l₂ u₂ l₃ u₃ l₄ u₄ : UInt8) → ∀ {@0 bs} → UTF8Char4 bs → Set
InRangeUTF8Char4 l₁ u₁ l₂ u₂ l₃ u₃ l₄ u₄ x =
  InRange l₁ u₁ b₁ × InRange l₂ u₂ b₂ × InRange l₃ u₃ b₃ × InRange l₄ u₄ b₄
  where open UTF8Char4 x

RawUTF8Char4 : Raw UTF8Char4
Raw.D RawUTF8Char4 = Vec UInt8 4
Raw.to RawUTF8Char4 x = UTF8Char4.b₁ x ∷ UTF8Char4.b₂ x ∷ UTF8Char4.b₃ x ∷ Vec.[ UTF8Char4.b₄ x ]

data UTF8Char (@0 bs : List UInt8) : Set where
  utf81 : UTF8Char1 bs → UTF8Char bs
  utf82 : UTF8Char2 bs → UTF8Char bs
  utf83 : UTF8Char3 bs → UTF8Char bs
  utf84 : UTF8Char4 bs → UTF8Char bs

UTF8CharRep : @0 List UInt8 → Set
UTF8CharRep =
   Sum UTF8Char1
  (Sum UTF8Char2
  (Sum UTF8Char3
       UTF8Char4))

equivalentChar : Equivalent UTF8CharRep UTF8Char
proj₁ equivalentChar (inj₁ x) = utf81 x
proj₁ equivalentChar (inj₂ (inj₁ x)) = utf82 x
proj₁ equivalentChar (inj₂ (inj₂ (inj₁ x))) = utf83 x
proj₁ equivalentChar (inj₂ (inj₂ (inj₂ x))) = utf84 x
proj₂ equivalentChar (utf81 x) = inj₁ x
proj₂ equivalentChar (utf82 x) = inj₂ (inj₁ x)
proj₂ equivalentChar (utf83 x) = inj₂ (inj₂ (inj₁ x))
proj₂ equivalentChar (utf84 x) = inj₂ (inj₂ (inj₂ x))

InRangeUTF8Char : (n : Fin 4) (ranges : Vec (UInt8 × UInt8) (1 + toℕ n)) → ∀ {@0 bs} → UTF8Char bs → Set
InRangeUTF8Char Fin.zero ((l₁ , u₁) ∷ []) (utf81 x) =
  InRange l₁ u₁ (UTF8Char1.b₁ x)
InRangeUTF8Char Fin.zero ranges _ = ⊥
InRangeUTF8Char (Fin.suc Fin.zero) ((l₁ , u₁) ∷ (l₂ , u₂) ∷ []) (utf82 x) =
  InRangeUTF8Char2 l₁ u₁ l₂ u₂ x
InRangeUTF8Char (Fin.suc Fin.zero) ranges _ = ⊥
InRangeUTF8Char (Fin.suc (Fin.suc Fin.zero)) ((l₁ , u₁) ∷ (l₂ , u₂) ∷ (l₃ , u₃) ∷ []) (utf83 x) =
  InRangeUTF8Char3 l₁ u₁ l₂ u₂ l₃ u₃ x
InRangeUTF8Char (Fin.suc (Fin.suc Fin.zero)) ranges _ = ⊥
InRangeUTF8Char (Fin.suc (Fin.suc (Fin.suc Fin.zero))) ((l₁ , u₁) ∷ (l₂ , u₂) ∷ (l₃ , u₃) ∷ (l₄ , u₄) ∷ []) (utf84 x) =
  InRangeUTF8Char4 l₁ u₁ l₂ u₂ l₃ u₃ l₄ u₄ x
InRangeUTF8Char (Fin.suc (Fin.suc (Fin.suc Fin.zero))) _ _ = ⊥

RawUTF8CharRep : Raw UTF8CharRep
RawUTF8CharRep =
   RawSum RawUTF8Char1
  (RawSum RawUTF8Char2
  (RawSum RawUTF8Char3
          RawUTF8Char4))

RawUTF8Char : Raw UTF8Char
RawUTF8Char = Iso.raw equivalentChar RawUTF8CharRep

UTF8 : @0 List UInt8 → Set
UTF8 = IList UTF8Char

RawUTF8 : Raw UTF8
RawUTF8 = RawIList RawUTF8Char

module UTF8 where
  size : ∀ {@0 bs} → UTF8 bs → ℕ
  size utf8 = lengthIList utf8

instance
  -- TODO: come back to this if there are performance issues
  NumericUTF8Char : ∀ {@0 bs} → Numeric (UTF8Char bs)
  Numeric.toℕ NumericUTF8Char (utf81 x) =
     toℕ (UTF8Char1.b₁ x)
  Numeric.toℕ NumericUTF8Char (utf82 x) =
     toℕ (UTF8Char2.b₁ x) * (2 ^ 8) + toℕ (UTF8Char2.b₂ x)
  Numeric.toℕ NumericUTF8Char (utf83 x) =
     (toℕ $ UTF8Char3.b₁ x) * (2 ^ (8 * 2)) + (toℕ $ UTF8Char3.b₂ x) * (2 ^ 8) + toℕ (UTF8Char3.b₃ x)
  Numeric.toℕ NumericUTF8Char (utf84 x) =
      (toℕ $ UTF8Char4.b₁ x) * (2 ^ (8 * 3)) + (toℕ $ UTF8Char4.b₂ x) * 2 ^ (8 * 2)
    + (toℕ $ UTF8Char4.b₃ x) * 2 ^ 8 + (toℕ $ UTF8Char4.b₄ x)
