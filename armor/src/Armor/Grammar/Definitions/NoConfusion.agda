open import Armor.Prelude

module Armor.Grammar.Definitions.NoConfusion (Σ : Set) where

NoConfusion : (A B : @0 List Σ → Set) → Set
NoConfusion A B =
  ∀ {xs₁ ys₁ xs₂ ys₂}
  → (xs₁++ys₁≡xs₂++ys₂ : xs₁ ++ ys₁ ≡ xs₂ ++ ys₂)
  → (a : A xs₁) → ¬ B xs₂

@0 symNoConfusion : ∀ {A B} → NoConfusion A B → NoConfusion B A
symNoConfusion nc ++≡ v₂ v₁ = nc (sym ++≡) v₁ v₂
