open import Armor.Prelude

module Armor.Grammar.Definitions.NonEmpty (Σ : Set) where

NonEmpty : (A : @0 List Σ → Set) → Set
NonEmpty A = ∀ {xs : List Σ} → A xs → xs ≢ []

