open import Armor.Prelude renaming (Σ to Sigma)

module Armor.Grammar.Definitions.NonMalleable.Base (Σ : Set) where

record Raw (A : @0 List Σ → Set) : Set₁ where
  field
    D : Set
    to : {@0 xs : List Σ} → A xs → D

record Raw₁ {A : @0 List Σ → Set} (R : Raw A) (P : {@0 xs : List Σ} → A xs → @0 List Σ → Set) : Set₁ where
  field
    D : Raw.D R → Set
    to : ∀ {@0 bs₁} → (a : A bs₁) → ∀ {@0 bs₂} → P a bs₂ → D (Raw.to R a)

RawSubSingleton : ∀ {A} → Raw A
Raw.D RawSubSingleton = ⊤
Raw.to RawSubSingleton _ = tt

mapRaw : {A B : @0 List Σ → Set} → (∀ {@0 xs} → B xs → A xs) → Raw A → Raw B
Raw.D (mapRaw f r) = Raw.D r
Raw.to (mapRaw f r) b = Raw.to r (f b)

NonMalleable : {A : @0 List Σ → Set} → Raw A → Set
NonMalleable{A} R = ∀ {@0 bs₁ bs₂} → (a₁ : A bs₁) (a₂ : A bs₂) (eq : Raw.to R a₁ ≡ Raw.to R a₂) → _≡_{A = Exists─ (List Σ) A} (─ bs₁ , a₁) (─ bs₂ , a₂)

subsingleton⇒nonmalleable : {A : @0 List Σ → Set} → ((a₁ a₂ : Exists─ (List Σ) A) → a₁ ≡ a₂) → NonMalleable (RawSubSingleton{A})
subsingleton⇒nonmalleable ss a₁ a₂ _ = ss (─ _ , a₁) (─ _ , a₂)

NonMalleable₁ : {A : @0 List Σ → Set} {R : Raw A} {P : ∀ {@0 xs} → A xs → @0 List Σ → Set} (RP : Raw₁ R P) → Set
NonMalleable₁{A}{P = P} RP =
  ∀ {@0 bs} {a : A bs} → ∀ {@0 bs₁ bs₂} → (p₁ : P a bs₁) (p₂ : P a bs₂) → (eq : Raw₁.to RP a p₁ ≡ Raw₁.to RP a p₂)
  → _≡_{A = Exists─ (List Σ) (P a)} (─ bs₁ , p₁) (─ bs₂ , p₂)
