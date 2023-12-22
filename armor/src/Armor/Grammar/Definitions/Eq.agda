open import Armor.Prelude
  renaming (Σ to Sigma)

module Armor.Grammar.Definitions.Eq (Σ : Set) where

infix 4 _≋_
record _≋_ {A : @0 List Σ → Set} {@0 bs₁ bs₂} (a₁ : A bs₁) (a₂ : A bs₂) : Set where
  constructor mk≋
  field
    @0 bs≡ : bs₁ ≡ bs₂
    @0 a≡  : subst₀! A bs≡ a₁ ≡ a₂

pattern ≋-refl = mk≋ refl refl

trans≋ : ∀ {A : @0 List Σ → Set} {@0 bs₁ bs₂ bs₃} → {a₁ : A bs₁} {a₂ : A bs₂} {a₃ : A bs₃}
         → _≋_{A} a₁ a₂ → _≋_{A} a₂ a₃ → _≋_{A} a₁ a₃
trans≋ ≋-refl ≋-refl = ≋-refl

sym≋ : ∀ {A : @0 List Σ → Set} {@0 bs₁ bs₂} {a₁ : A bs₁} {a₂ : A bs₂}
       → _≋_{A} a₁ a₂ → _≋_{A} a₂ a₁
sym≋ ≋-refl = ≋-refl

cong≋ : ∀ {A B : @0 List Σ → Set} {@0 bs₁ bs₂} {a₁ : A bs₁} {a₂ : A bs₂}
        → (f : ∀ {@0 bs} → A bs → Exists─ (List Σ) B)
        → _≋_{A} a₁ a₂ → _≋_{B} (proj₂ (f a₁)) (proj₂ (f a₂))
cong≋ f ≋-refl = ≋-refl

unique≋ : ∀ {A : @0 List Σ → Set} {@0 bs₁ bs₂ : List Σ}
          → (a₁ : A bs₁) (a₂ : A bs₂) → Unique (_≋_{A = A} a₁ a₂)
unique≋ a₁ a₂ ≋-refl ≋-refl = refl

instance
  Irrel≋ : ∀ {@0 A bs₁ bs₂} {a₁ : A bs₁} {a₂ : A bs₂} → Irrel (_≋_{A} a₁ a₂)
  Irrel.irrel Irrel≋ ≋-refl = ≋-refl

Decidable-≋ : (@0 List Σ → Set) → Set
Decidable-≋ A = ∀ {@0 bs₁ bs₂} (a₁ : A bs₁) (a₂ : A bs₂) → Dec (_≋_{A} a₁ a₂)

record Eq≋ (@0 A : @0 List Σ → Set) : Set where
  infix 4 _≋?_
  field
    _≋?_ : Decidable-≋ A

open Eq≋ ⦃ ... ⦄ public

Eq≋⇒Eq : ∀ {@0 A : @0 List Σ → Set} → Eq≋ A → Eq (Exists─ (List Σ) A)
Eq._≟_ (Eq≋⇒Eq eq≋) (─ bs₁ , a₁) (─ bs₂ , a₂) =
  case Eq≋._≋?_ eq≋ a₁ a₂ ret (const _) of λ where
    (no ¬p) → no₀ λ where refl → contradiction ≋-refl ¬p
    (yes (mk≋ refl refl)) → yes₀ (‼ (refl{x = ─ bs₁ ,e a₁}))

Eq⇒Eq≋ : ∀ {A : @0 List Σ → Set} → Eq (Exists─ (List Σ) A) → Eq≋ A
Eq≋._≋?_ (Eq⇒Eq≋ eq) a₁ a₂ =
  case Eq._≟_ eq (─ _ , a₁) (─ _ , a₂) ret (const _) of λ where
    (no ¬p) → no₀ λ where ≋-refl → contradiction refl ¬p
    (yes refl) → yes₀ ≋-refl

