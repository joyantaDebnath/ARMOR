open import Armor.Prelude

module Armor.Grammar.Definitions.NoSubstrings (Σ : Set) where

NoSubstrings : (A : @0 List Σ → Set) → Set
NoSubstrings A =
  ∀ {xs₁ ys₁ xs₂ ys₂} → (xs₁++ys₁≡xs₂++ys₂ : xs₁ ++ ys₁ ≡ xs₂ ++ ys₂)
  → (a₁ : A xs₁) (a₂ : A xs₂) → xs₁ ≡ xs₂
