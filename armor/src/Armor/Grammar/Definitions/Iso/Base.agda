open import Armor.Prelude

module Armor.Grammar.Definitions.Iso.Base (Σ : Set) where

Equivalent : (A B : @0 List Σ → Set) → Set
Equivalent A B = (∀ {@0 xs} → A xs → B xs) × (∀ {@0 xs} → B xs → A xs)

Iso : (A B : @0 List Σ → Set) → Set
Iso A B = Σ[ e ∈ Equivalent A B ]
            ((∀ {@0 xs} → proj₂ e ∘ proj₁ e ≗ id{A = A xs}) × (∀ {@0 xs} → proj₁ e ∘ proj₂ e ≗ id{A = B xs}))

