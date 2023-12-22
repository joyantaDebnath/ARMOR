import      Armor.Grammar.Definitions
open import Armor.Prelude

module Armor.Grammar.Serializer (Σ : Set) where

Serializer : (A : @0 List Σ → Set) → Set
Serializer A = ∀ {@0 bs} → A bs → Singleton bs

open Armor.Grammar.Definitions Σ

-- serializeEquivalent : ∀ {@0 A B} → Equivalent A B → Serializer A → Serializer B
-- serializeEquivalent (fst , snd) sa b = sa (snd b)

-- serialize&ₚ : ∀ {@0 A B} → Serializer A → Serializer B → Serializer (&ₚ A B)
-- Singleton.x (serialize&ₚ sa sb  (mk&ₚ fstₚ₁ sndₚ₁ bs≡)) =
--   Singleton.x (sa fstₚ₁) ++ Singleton.x (sb sndₚ₁)
-- Singleton.x≡ (serialize&ₚ sa sb (mk&ₚ{bs₁}{bs₂} fstₚ₁ sndₚ₁ bs≡)) =
--   begin Singleton.x (sa fstₚ₁) ++ Singleton.x (sb sndₚ₁)
--           ≡⟨ cong₂ _++_ (Singleton.x≡ (sa fstₚ₁)) (Singleton.x≡ (sb sndₚ₁)) ⟩
--         bs₁ ++ bs₂
--           ≡⟨ sym bs≡ ⟩
--         _ ∎
--   where
--   open import Relation.Binary.PropositionalEquality
--   open ≡-Reasoning
