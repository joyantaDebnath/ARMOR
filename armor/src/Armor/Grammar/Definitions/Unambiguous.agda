open import Armor.Prelude

module Armor.Grammar.Definitions.Unambiguous (Σ : Set) where

-- `A` is unambiguous iff there is only one way for a given string to be
-- accepted by the grammar

Unambiguous : (A : @0 List Σ → Set) → Set
Unambiguous A = ∀ {xs} → (a₁ a₂ : A xs) → a₁ ≡ a₂

UnambiguousHet : (A : @0 List Σ → Set) → Set
UnambiguousHet A = ∀ {xs ys} → (eq : xs ≡ ys) (a₁ : A xs) (a₂ : A ys)
                   → subst₀! A eq a₁ ≡ a₂

unambiguousHet : ∀ {A : @0 List Σ → Set} → Unambiguous A → UnambiguousHet A
unambiguousHet ua refl a₁ a₂ = ua a₁ a₂
