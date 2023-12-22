open import Armor.Prelude
import      Armor.Grammar.Definitions
open import Data.Nat.Properties
  hiding (_≟_)

module Armor.Grammar.Parser.Core (Σ : Set) where

open Armor.Grammar.Definitions Σ

record Success (A : @0 List Σ → Set) (@0 xs : List Σ) : Set where
  constructor success
  field
    @0 prefix : List Σ
    read   : ℕ
    @0 read≡ : read ≡ length prefix
    value  : A prefix
    suffix : List Σ
    @0 ps≡    : prefix ++ suffix ≡ xs

mapSuccess : ∀ {A B : @0 List Σ → Set} → (∀ {@0 xs} → A xs → B xs) → ∀ {@0 xs} → Success A xs → Success B xs
mapSuccess f (success prefix read read≡ value suffix ps≡ ) = success prefix read read≡ (f value) suffix ps≡

record Parserᵢ (M : List Σ → Set → Set) (A : @0 List Σ → Set) : Set where
  constructor mkParser
  field
    runParser : (xs : List Σ) → M xs (Success A xs)
open Parserᵢ public

Parser : (M : Set → Set) (A : @0 List Σ → Set) → Set
Parser M = Parserᵢ (const M)

module _ {M : Set → Set} ⦃ _ : Monad M ⦄ where

  parseEquivalent : {A B : @0 List Σ → Set} → Equivalent A B
                    → Parser (M ∘ Dec) A → Parser (M ∘ Dec) B
  runParser (parseEquivalent (eq₁ , eq₂) p) xs = do
    yes x ← runParser p xs
      where no ¬parse → do
        return ∘ no $ contraposition (mapSuccess eq₂) ¬parse
    return (yes
      (mapSuccess eq₁ x))

  parseErased : {A : @0 List Σ → Set} → Parser (M ∘ Dec) A → Parser (M ∘ Dec) (λ x → Erased (A x))
  runParser (parseErased p) xs = do
    yes x ← runParser p xs
      where no ¬p → do
        return ∘ no $ λ where
          (success prefix read read≡ (─ x) suffix ps≡) →
            contradiction (success prefix _ read≡ x suffix ps≡) ¬p
    return (yes (mapSuccess (λ x → ─ x) x))

  parser2dec
    : (extract : ∀ {A} → M A → A)
      → {A : @0 List Σ → Set} → @0 NoSubstrings A
      → Parser (M ∘ Dec) A → Decidable (λ x → A x)
  parser2dec extract {A} nn p xs =
    case extract (runParser p xs) of λ where
      (no ¬p) → no λ a →
        contradiction
          (success xs _ refl a [] (++-identityʳ _))
          ¬p
      (yes (success prefix read read≡ value (c ∷ suffix) ps≡)) →
        no λ a → ‼
          let @0 ps≡' : prefix ++ c ∷ suffix ≡ xs ++ []
              ps≡' = trans ps≡ (sym $ ++-identityʳ _)
          in
          contradiction{P = _≡_{A = List Σ} (c ∷ suffix) []}
            (Lemmas.++-cancel≡ˡ _ _
              (nn ps≡' value a) ps≡')
            λ ()
      (yes (success prefix read read≡ value [] ps≡)) →
        yes (subst₀! A (trans (sym $ ++-identityʳ _) ps≡) value)

  parseFalse : Parser (M ∘ Dec) (λ _ → ⊥)
  runParser parseFalse xs = return ∘ no $ λ ()
