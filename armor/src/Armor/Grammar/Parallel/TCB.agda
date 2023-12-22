import      Armor.Grammar.Definitions.NonMalleable.Base
open import Armor.Prelude
open import Data.Nat.Properties

module Armor.Grammar.Parallel.TCB (Σ : Set) where

open Armor.Grammar.Definitions.NonMalleable.Base Σ

record Σₚ (A : @0 List Σ → Set) (B : (@0 xs : List Σ) (a : A xs) → Set) (@0 xs : List Σ) : Set where
  constructor mk×ₚ
  field
    fstₚ : A xs
    sndₚ : B xs fstₚ
open Σₚ public using (fstₚ ; sndₚ)

_×ₚ_ : (A B : @0 List Σ → Set) (@0 xs : List Σ) → Set
A ×ₚ B = Σₚ A (λ xs _ → B xs)

-- Raw values that drop the second component (for when it is only specificational)
RawΣₚ₁ : {A : @0 List Σ → Set} → Raw A → (B : (@0 xs : List Σ) (a : A xs) → Set) → Raw (Σₚ A B)
Raw.D (RawΣₚ₁ r B) = Raw.D r
Raw.to (RawΣₚ₁ r B) (mk×ₚ a _) = Raw.to r a

Raw×ₚ : {A B : @0 List Σ → Set} → Raw A → Raw B → Raw (A ×ₚ B)
Raw.D (Raw×ₚ ra rb) = Raw.D ra × Raw.D rb
Raw.to (Raw×ₚ ra rb) (mk×ₚ a b) = (Raw.to ra a) , (Raw.to rb b)

map×ₚ : ∀ {@0 A₁ A₂ B} → (∀ {@0 xs} → A₁ xs → A₂ xs) → (∀ {@0 xs} → (A₁ ×ₚ B) xs → (A₂ ×ₚ B) xs)
map×ₚ f (mk×ₚ fstₚ₁ sndₚ₁) = mk×ₚ (f fstₚ₁) sndₚ₁

-- type definitions that place restrictions on the length of the string
--- bounded below
Length≥ : (A : @0 List Σ → Set) → ℕ → @0 List Σ → Set
Length≥ A n = A ×ₚ (λ x → Erased (length x ≥ n))

--- bounded above
Length≤ : (A : @0 List Σ → Set) → ℕ → (@0 _ : List Σ) → Set
Length≤ A n = A ×ₚ (λ x → Erased (length x ≤ n))

-- Bounded : (@0 A : List Σ → Set) (@0 l u : ℕ) → @0 List Σ → Set
-- Bounded A l u = A ×ₚ (InRange l u ∘ length)

--- bounded exactly
ExactLength : (A : @0 List Σ → Set) → @0 ℕ → @0 List Σ → Set
ExactLength A n = A ×ₚ (λ x → Erased (length x ≡ n))

ExactLengthString : ℕ → @0 List Σ → Set
ExactLengthString n = ExactLength Singleton n

mkExactLengthString : (n : ℕ) → (xs : List Σ) → (len≡ : length xs ≡ n) → ExactLengthString n xs
mkExactLengthString n xs len≡ = mk×ₚ self (─ len≡)

lookupExactLengthString : ∀ {@0 xs} {n} (s : ExactLengthString n xs) → Fin n → Σ
lookupExactLengthString (mk×ₚ (singleton (x ∷ x₁) refl) _) Fin.zero = x
lookupExactLengthString (mk×ₚ (singleton (x ∷ x₁) refl) (─ sndₚ₁)) (Fin.suc i) =
  lookupExactLengthString (mk×ₚ (singleton x₁ refl) (─ (suc-injective sndₚ₁))) i
