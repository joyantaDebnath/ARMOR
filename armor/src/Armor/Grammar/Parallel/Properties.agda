-- TODO: make this depend on Armor.Grammar.Definitions once dependencies have
-- been sorted out
import      Armor.Grammar.Definitions.Eq
import      Armor.Grammar.Definitions.Iso
import      Armor.Grammar.Definitions.NoConfusion
import      Armor.Grammar.Definitions.NoSubstrings
import      Armor.Grammar.Definitions.NonEmpty
import      Armor.Grammar.Definitions.NonMalleable.Base
import      Armor.Grammar.Definitions.Unambiguous
import      Armor.Grammar.Parallel.TCB
open import Armor.Prelude

module Armor.Grammar.Parallel.Properties (Σ : Set) where

open Armor.Grammar.Definitions.Eq                Σ
open Armor.Grammar.Definitions.Iso               Σ
open Armor.Grammar.Definitions.NoConfusion       Σ
open Armor.Grammar.Definitions.NoSubstrings      Σ
open Armor.Grammar.Definitions.NonEmpty          Σ
open Armor.Grammar.Definitions.NonMalleable.Base Σ
open Armor.Grammar.Definitions.Unambiguous       Σ
open Armor.Grammar.Parallel.TCB                  Σ


module Parallel where
  equivalent₁ : ∀ {A₁ A₂ B : @0 List Σ → Set} → Equivalent A₁ A₂ → Equivalent (A₁ ×ₚ B) (A₂ ×ₚ B)
  proj₁ (equivalent₁ equiv) (mk×ₚ fstₚ₁ sndₚ₁) = mk×ₚ (proj₁₀ equiv fstₚ₁) sndₚ₁
  proj₂ (equivalent₁ equiv) (mk×ₚ fstₚ₁ sndₚ₁) = mk×ₚ (proj₂₀ equiv fstₚ₁) sndₚ₁

  @0 noconfusion₁ : ∀ {A₁ A₂ B} → NoConfusion A₁ A₂ → NoConfusion (Σₚ A₁ B) A₂
  noconfusion₁ nc xs₁++ys₁≡xs₂++ys₂ (mk×ₚ fstₚ₁ sndₚ₁) x =
    nc xs₁++ys₁≡xs₂++ys₂ fstₚ₁ x

  @0 noconfusionΣₚ₁ : ∀ {A₁ A₂ B₁ B₂} → NoConfusion A₁ A₂ → NoConfusion (Σₚ A₁ B₁) (Σₚ A₂ B₂)
  noconfusionΣₚ₁{A₁}{A₂}{B₁}{B₂} nc =
    noconfusion₁{A₂ = Σₚ A₂ B₂}
      (symNoConfusion{A = Σₚ A₂ B₂}{B = A₁}
        (noconfusion₁{A₁ = A₂}{A₂ = A₁}
          (symNoConfusion{A = A₁}{B = A₂} nc)))

  @0 nosubstrings₁ : ∀ {A B} → NoSubstrings A → NoSubstrings (Σₚ A B)
  nosubstrings₁ ns xs₁++ys₁≡xs₂++ys₂ (mk×ₚ fstₚ₁ sndₚ₁) (mk×ₚ fstₚ₂ sndₚ₂) =
    ns xs₁++ys₁≡xs₂++ys₂ fstₚ₁ fstₚ₂

  @0 nosubstrings₂ : ∀ {A B} → NoSubstrings B → NoSubstrings (A ×ₚ B)
  nosubstrings₂ ns xs₁++ys₁≡xs₂++ys₂ (mk×ₚ fstₚ₁ sndₚ₁) (mk×ₚ fstₚ₂ sndₚ₂) =
    ns xs₁++ys₁≡xs₂++ys₂ sndₚ₁ sndₚ₂
  
  @0 nonempty₁ : ∀ {A B} → NonEmpty A → NonEmpty (Σₚ A B)
  nonempty₁ ne (mk×ₚ fstₚ₁ sndₚ₁) xs≡[] = contradiction xs≡[] (ne fstₚ₁)
  
  @0 unambiguous : ∀ {A B} → Unambiguous A → (∀ {xs} a → Unique (B xs a)) → Unambiguous (Σₚ A B)
  unambiguous ua ub (mk×ₚ fstₚ₁ sndₚ₁) (mk×ₚ fstₚ₂ sndₚ₂) =
    case ua fstₚ₁ fstₚ₂ of λ where
      refl → case ub fstₚ₁ sndₚ₁ sndₚ₂ of λ where
        refl → refl

  @0 unambiguous×ₚ : ∀ {A B} → Unambiguous A → Unambiguous B → Unambiguous (A ×ₚ B)
  unambiguous×ₚ ua ub = unambiguous ua λ _ → ub

  eqΣₚ : ∀ {A : @0 List Σ → Set} {B : (@0 xs : List Σ) → A xs → Set}
         → Eq (Exists─ (List Σ) A)
         → (∀ {@0 bs} → (a : A bs) → Eq (B bs a))
         → Eq (Exists─ (List Σ) (Σₚ A B))
  Eq._≟_ (eqΣₚ eq₁ eq₂) (─ bs₁ , mk×ₚ a₁ b₁) (─ bs₂ , mk×ₚ a₂ b₂) =
    case Eq._≟_ eq₁ (─ bs₁ , a₁) (─ bs₂ , a₂) ret (const _) of λ where
      (no ¬p) → no (λ where refl → contradiction refl ¬p)
      (yes refl) →
        case Eq._≟_ (eq₂ a₁) b₁ b₂ ret (const _) of λ where
          (no ¬p) → no λ where refl → contradiction refl ¬p
          (yes refl) → yes refl

  eq≋Σₚ : ∀ {A : @0 List Σ → Set} {B : (@0 xs : List Σ) → A xs → Set} → Eq≋ A
          → (∀ {@0 bs} → (a : A bs) → Eq (B bs a))
          → Eq≋ (Σₚ A B)
  eq≋Σₚ eq₁ eq₂ = Eq⇒Eq≋ (eqΣₚ (Eq≋⇒Eq eq₁) eq₂) 

  @0 nonmalleable₁
    : {A : @0 List Σ → Set} {B : (@0 xs : List Σ) → A xs → Set}
      → (rₐ : Raw A) → NonMalleable rₐ → (∀ {xs} (a : A xs) → Unique (B _ a))
      → NonMalleable (RawΣₚ₁ rₐ B)
  nonmalleable₁ rₐ nm ub (mk×ₚ fstₚ₁ sndₚ₁) (mk×ₚ fstₚ₂ sndₚ₂) eq =
    case nm fstₚ₁ fstₚ₂ eq ret (const _) of λ where
      refl → case (‼ ub _ sndₚ₁ sndₚ₂) ret (const _) of λ where
        refl → refl

  @0 nonmalleable×ₚ
    : {A B : @0 List Σ → Set} {ra : Raw A} {rb : Raw B}
      → NonMalleable ra → NonMalleable rb → NonMalleable (Raw×ₚ ra rb)
  nonmalleable×ₚ nm₁ nm₂ (mk×ₚ a₁ b₁) (mk×ₚ a₂ b₂) eq =
    case nm₁ a₁ a₂ (cong proj₁ eq) ,′ nm₂ b₁ b₂ (cong (λ x → proj₂ x) eq) ret (const _) of λ where
      (refl , refl) → refl

module ExactLength {n : ℕ} (A : @0 List Σ → Set) where
  @0 nosubstrings : NoSubstrings (ExactLength A n)
  nosubstrings xs₁++ys₁≡xs₂++ys₂ (mk×ₚ fstₚ₁ sndₚ₁) (mk×ₚ fstₚ₂ sndₚ₂) =
    proj₁ (Lemmas.length-++-≡ _ _ _ _ xs₁++ys₁≡xs₂++ys₂ (trans₀ (¡ sndₚ₁) (sym (¡ sndₚ₂))))

  @0 unambiguous : Unambiguous A → Unambiguous (ExactLength A n)
  unambiguous ua = Parallel.unambiguous ua λ _ → erased-unique ≡-unique

  instance
    eq≋ : ⦃ _ : Eq≋ A ⦄ → Eq≋ (ExactLength A n)
    eq≋ ⦃ eq ⦄ = Parallel.eq≋Σₚ eq λ a → record { _≟_ = λ x y → yes (‼ erased-unique ≡-unique x y) }

module ExactLengthString {n : ℕ} where
  @0 unambiguous : Unambiguous (ExactLengthString n)
  unambiguous = ExactLength.unambiguous Singleton uniqueSingleton

module Length≥ {n : ℕ} (A : @0 List Σ → Set) where
  @0 unambiguous : Unambiguous A → Unambiguous (Length≥ A n)
  unambiguous ua = Parallel.unambiguous ua λ _ → erased-unique ≤-unique

module Length≤ {n : ℕ} (A : @0 List Σ → Set) where
  @0 unambiguous : Unambiguous A → Unambiguous (Length≤ A n)
  unambiguous ua = Parallel.unambiguous ua λ _ → erased-unique ≤-unique

open Parallel public
