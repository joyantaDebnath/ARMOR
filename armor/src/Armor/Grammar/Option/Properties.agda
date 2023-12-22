import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel.TCB
import      Armor.Grammar.Option.TCB
open import Armor.Prelude
import      Data.Nat.Properties as Nat
open import Data.Maybe.Properties

module Armor.Grammar.Option.Properties (Σ : Set) where

open Armor.Grammar.Definitions  Σ
open Armor.Grammar.Option.TCB   Σ
open Armor.Grammar.Parallel.TCB Σ

equivNonEmpty : ∀ {A : @0 List Σ → Set} → @0 NonEmpty A
                → Equivalent (Length≥ (Option A) 1) A
proj₁ (equivNonEmpty ne) (mk×ₚ (some x) sndₚ₁) = x
proj₂ (equivNonEmpty ne) {xs}x =
  mk×ₚ (some x) (─ (Nat.n≢0⇒n>0 (λ x₁ → contradiction (proj₁ (Lemmas.length-++-≡ _ [] _ xs (++-identityʳ xs) x₁)) (ne x))))

instance
  OptionEq≋ : ∀ {A : @0 List Σ → Set} ⦃ _ : Eq≋ A ⦄ → Eq≋ (Option A)
  Eq≋._≋?_ OptionEq≋ {.[]} {.[]} none none = yes ≋-refl
  Eq≋._≋?_ OptionEq≋ {.[]} {bs₂} none (some x) = no (λ where (mk≋ refl ()))
  Eq≋._≋?_ OptionEq≋ {bs₁} {.[]} (some x) none = no λ where (mk≋ refl ())
  Eq≋._≋?_ OptionEq≋ {bs₁} {bs₂} (some v₁) (some v₂) =
    case v₁ ≋? v₂ of λ where
      (yes ≋-refl) → yes ≋-refl
      (no  ¬v₁≋v₂) → no λ where
        ≋-refl → contradiction ≋-refl ¬v₁≋v₂

  OptionEq
    : ∀ {A : @0 List Σ → Set} ⦃ _ : Eq (Exists─ (List Σ) A) ⦄
      → Eq (Exists─ (List Σ) (Option A))
  OptionEq = Eq≋⇒Eq (OptionEq≋ ⦃ Eq⇒Eq≋ it ⦄)

@0 unambiguous : ∀ {A} → Unambiguous A → NonEmpty A → Unambiguous (Option A)
unambiguous ua ne none none = refl
unambiguous ua ne none (some x) = contradiction refl (ne x)
unambiguous ua ne (some x) none = contradiction refl (ne x)
unambiguous ua ne (some x) (some x₁) = ‼ cong some (ua x x₁)

@0 nonmalleable : ∀ {A} → (r : Raw A) → NonMalleable r → NonMalleable (RawOption r) 
nonmalleable r x none none eq = refl
nonmalleable r x (some x₁) (some x₂) eq = case x x₁ x₂ (just-injective eq) ret (const _) of λ where
  refl → refl
