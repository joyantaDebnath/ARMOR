open import Armor.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Armor.Grammar.Parser.Lit (Σ : Set) where

open import Armor.Grammar.Definitions Σ
open import Armor.Grammar.Parser.Core Σ

parseLit : {M : Set → Set} ⦃ _ : Monad M ⦄ ⦃ _ : Eq Σ ⦄ → (underflow mismatch : M (Level.Lift _ ⊤))
           → (lit : List Σ) → Parser (M ∘ Dec) (_≡ lit)
runParser (parseLit underflow mismatch []) xs = return (yes (success [] 0 refl refl xs refl))
runParser (parseLit underflow mismatch (l ∷ lit)) [] = do
  underflow
  return ∘ no $ λ where
    (success .(l ∷ lit) read read≡ refl suffix ())
runParser (parseLit underflow mismatch (l ∷ lit)) (x ∷ xs)
  with x ≟ l
... | no ¬x≡l = do
  mismatch
  return ∘ no $ λ where
    (success .(l ∷ lit) read read≡ refl suffix ps≡) →
      contradiction (sym (∷-injectiveˡ ps≡)) ¬x≡l
... | yes refl = do
  yes (success pre₀ _ r₀≡ refl suf₀ refl) ← runParser (parseLit underflow mismatch lit) xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success .(l ∷ lit) read read≡ refl suffix ps≡) →
          contradiction (success lit _ (cong pred read≡) refl suffix (∷-injectiveʳ ps≡)) ¬parse
  return (yes (success (l ∷ pre₀) _ (cong suc r₀≡) refl suf₀ refl))

parseLitE
  : {M : Set → Set} ⦃ _ : Monad M ⦄ ⦃ _ : Eq Σ ⦄ → (underflow mismatch : M (Level.Lift _ ⊤))
    → (lit : List Σ) → Parser (M ∘ Dec) (λ x → Erased (x ≡ lit))
runParser (parseLitE underflow mismatch lit) xs = do
  yes s ← runParser (parseLit underflow mismatch lit) xs
    where no ¬p → return ∘ no $ λ where
      s → contradiction (mapSuccess (λ x → ¡ x) s) ¬p
  return (yes (mapSuccess (λ x → ─ x) s))
