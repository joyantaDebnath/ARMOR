import      Armor.Grammar.IList.TCB
open import Armor.Prelude
  hiding (module All; All)

module Armor.Grammar.IList.All (Σ : Set) where

open Armor.Grammar.IList.TCB Σ

data All {A : @0 List Σ → Set} (P : ∀ {@0 bs} → A bs → Set) : ∀ {@0 bs} → IList A bs → Set where
  [] : All P nil
  cons : ∀ {@0 bs₁ bs₂ bs} → (x : A bs₁) → P x → (xs : IList A bs₂) → All P xs → (@0 bs≡ : bs ≡ bs₁ ++ bs₂)
         → All P (consIList x xs bs≡)

all? : ∀ {@0 A} {@0 P : ∀ {bs} → A bs → Set} → (∀ {@0 bs} → (a : A bs) → Dec (P a)) → ∀ {@0 bs} → (xs : IList A bs) → Dec (All P xs)
all? d nil = yes []
all? d (consIList h₁ t₁ bs≡)
  with d h₁
... | no ¬p = no λ where
  (cons .h₁ x .t₁ x₁ .bs≡) → contradiction x ¬p
... | yes p
  with all? d t₁
... | no ¬p = no λ where
  (cons .h₁ x .t₁ x₁ .bs≡) → contradiction x₁ ¬p
... | yes p₁ = yes (cons h₁ p t₁ p₁ bs≡)
