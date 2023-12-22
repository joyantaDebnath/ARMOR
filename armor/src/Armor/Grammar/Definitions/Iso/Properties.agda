import      Armor.Grammar.Definitions.Eq
import      Armor.Grammar.Definitions.Iso.Base
import      Armor.Grammar.Definitions.NoSubstrings
import      Armor.Grammar.Definitions.NonEmpty
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.Definitions.Unambiguous
open import Armor.Prelude
import      Data.Product.Properties as Product

module Armor.Grammar.Definitions.Iso.Properties (Σ : Set) where

open Armor.Grammar.Definitions.Eq           Σ
open Armor.Grammar.Definitions.Iso.Base     Σ
open Armor.Grammar.Definitions.NoSubstrings Σ
open Armor.Grammar.Definitions.NonEmpty     Σ
open Armor.Grammar.Definitions.NonMalleable Σ
open Armor.Grammar.Definitions.Unambiguous  Σ

symEquivalent : ∀ {A B} → Equivalent A B → Equivalent B A
symEquivalent (fst , snd) = snd , fst

transEquivalent : ∀ {A B C} → Equivalent A B → Equivalent B C → Equivalent A C
proj₁ (transEquivalent e₁ e₂) = proj₁ e₂ ∘ proj₁ e₁
proj₂ (transEquivalent e₁ e₂) = proj₂ e₁ ∘ proj₂ e₂

symIso : ∀ {A B} → Iso A B → Iso B A
proj₁ (symIso x) = symEquivalent (proj₁ x)
proj₁ (proj₂ (symIso ((eq₁ , eq₂) , iso))) = proj₂ iso
proj₂ (proj₂ (symIso ((eq₁ , eq₂) , iso))) = proj₁ iso

nonempty : ∀ {@0 A B} → Equivalent A B → NonEmpty A → NonEmpty B
nonempty eqv ne b ≡[] = contradiction ≡[] (ne (proj₂ eqv b))

nosubstrings : ∀ {@0 A B} → Equivalent A B → NoSubstrings A → NoSubstrings B
nosubstrings{A}{B} eqv nn ++≡ b₁ b₂ = ‼ nn ++≡ (proj₂ eqv b₁) (proj₂ eqv b₂)

unambiguous : ∀ {A B} → Iso A B → Unambiguous A → Unambiguous B
unambiguous ((a→b , b→a) , _ , id₂) ua{xs} b₁ b₂ =
  subst₂ _≡_ (id₂ b₁) (id₂ b₂) (‼ b≡)
  where
  @0 a≡ : b→a b₁ ≡ b→a b₂
  a≡ = ua (b→a b₁) (b→a b₂)

  @0 b≡ : a→b (b→a b₁) ≡ a→b (b→a b₂)
  b≡ = cong a→b a≡

injective₁ : ∀ {A B} → (x : Iso A B) → let equiv = proj₁ x in
             ∀ {@0 bs} {a₁ a₂ : A bs} → proj₁ equiv a₁ ≡ proj₁ equiv a₂ → a₁ ≡ a₂
injective₁ (equiv , iso){a₁ = a₁}{a₂} eq =
  a₁ ≡⟨ sym (proj₁ iso a₁) ⟩
  proj₂ equiv (proj₁ equiv a₁) ≡⟨ cong (proj₂ equiv) eq ⟩
  proj₂ equiv (proj₁ equiv a₂) ≡⟨ proj₁ iso a₂ ⟩
  a₂ ∎
  where
  open ≡-Reasoning

injective₂ : ∀ {A B} → (x : Iso A B) → let equiv = proj₁ x in
             ∀ {@0 bs} {a₁ a₂ : B bs} → proj₂ equiv a₁ ≡ proj₂ equiv a₂ → a₁ ≡ a₂
injective₂ (equiv , iso){a₁ = a₁}{a₂} eq = begin
  a₁ ≡⟨ sym (proj₂ iso a₁) ⟩
  proj₁ equiv (proj₂ equiv a₁) ≡⟨ cong (proj₁ equiv) eq ⟩
  proj₁ equiv (proj₂ equiv a₂) ≡⟨ proj₂ iso a₂  ⟩
  a₂ ∎
  where
  open ≡-Reasoning


raw : ∀ {A B} → Equivalent A B → Raw A → Raw B
Raw.D (raw equiv r) = Raw.D r
Raw.to (raw equiv r) b = Raw.to r (proj₂ equiv b)

@0 nonmalleable : ∀ {A B} → (iso : Iso A B) (r₁ : Raw A) → NonMalleable r₁ → NonMalleable (raw (proj₁ iso) r₁)
nonmalleable (equiv , isIso) r₁ nm a₁ a₂ eq =
  case
    Inverse.f⁻¹ Product.Σ-≡,≡↔≡ (nm (proj₂ equiv a₁) (proj₂ equiv a₂) eq)
  of λ where
    (refl , eq') → case injective₂ (equiv , isIso) eq' of λ where
      refl → refl

isoEq : ∀ {@0 A B} → Iso A B → Eq (Exists─ (List Σ) A) → Eq (Exists─ (List Σ) B)
Eq._≟_ (isoEq{A}{B} iso eq) (─ bs₁ , x) (─ bs₂ , y) =
  case _≟_ ⦃ eq ⦄ x“ y“ ret (const _) of λ where
    (no ¬p) →
      no₀ λ where
        refl →
          contradiction refl ¬p
    (yes p) →
      case (‼ cong (proj₁₀{B = λ y → A (Erased.x y)}) p) ret (const _) of λ where
        refl →
          yes₀ (‼ (begin
            (─ bs₁ , x) ≡⟨ cong (λ z → ─ bs₁ , z) (sym (proj₂₀ (proj₂₀ iso) x)) ⟩
            (─ bs₁ , proj₁ (proj₁₀ iso) x')
              ≡⟨ cong (λ z → ─ bs₁ , proj₁ (proj₁₀ iso) z)
                   (‼ ≡-elim{A = Exists─ (List Σ) A}
                     (λ {z“} eq →
                         x' ≡ subst (λ y → A (Erased.x y)) (trans (sym (erasedEta (proj₁₀ z“))) (cong proj₁₀ (sym eq))) (proj₂₀ z“))
                     refl p)
               ⟩
            (─ bs₁
            , proj₁ (proj₁₀ iso)
                (subst (λ y → A (Erased.x y)) (─ bs₁ ≡ ─ bs₁ ∋ cong proj₁₀ (sym p)) y'))
              ≡⟨ ≡-elimₖ
                   (λ eq → (─ bs₁ , proj₁ (proj₁₀ iso) (subst (λ y → A (Erased.x y)) eq y')) ≡ _)
                   refl (cong proj₁₀ (sym p)) ⟩
            (─ bs₁ , proj₁ (proj₁₀ iso) y') ≡⟨ cong (λ z → ─ bs₁ , z) (proj₂ (proj₂₀ iso) y) ⟩
            (─ bs₁ , y) ∎))

  where
  open ≡-Reasoning

  x' : A bs₁
  x' = proj₂₀ (proj₁₀{A = Equivalent A B} iso){bs₁} x

  x“ : Exists─ (List Σ) A
  x“ = (─ bs₁) , x'

  y' : A bs₂
  y' = proj₂₀ (proj₁₀{A = Equivalent A B} iso){bs₂} y

  y“ : Exists─ (List Σ) A
  y“ = (─ bs₂) , y'

isoEq≋ : ∀ {A B : @0 List Σ → Set} → Iso A B → Eq≋ A → Eq≋ B
isoEq≋ iso eq = Eq⇒Eq≋ (isoEq iso (Eq≋⇒Eq eq))

