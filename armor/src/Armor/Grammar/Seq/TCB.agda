import      Armor.Grammar.Definitions.NonMalleable.Base
open import Armor.Prelude renaming (Σ to Sigma)

module Armor.Grammar.Seq.TCB (Σ : Set) where

open Armor.Grammar.Definitions.NonMalleable.Base Σ

record &ₚᵈ (A : @0 List Σ → Set) (B : {@0 bs₁ : List Σ} → A bs₁ → @0 List Σ → Set) (@0 bs : List Σ) : Set where
  constructor mk&ₚ
  field
    @0 {bs₁ bs₂} : List Σ
    fstₚ : A bs₁
    sndₚ : B fstₚ bs₂
    @0 bs≡ : bs ≡ bs₁ ++ bs₂
open &ₚᵈ public using (fstₚ ; sndₚ)

&ₚ : (A B : @0 List Σ → Set) (@0 bs : List Σ) → Set
&ₚ A B = &ₚᵈ A λ _ → B

Raw&ₚᵈ : {A : @0 List Σ → Set} {B : {@0 bs : List Σ} → A bs → @0 List Σ → Set} → (ra : Raw A) (rb : Raw₁ ra B)
        → Raw (&ₚᵈ A B)
Raw.D  (Raw&ₚᵈ ra rb) = Sigma (Raw.D ra) (Raw₁.D rb)
Raw.to (Raw&ₚᵈ ra rb) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = (Raw.to ra fstₚ₁) , (Raw₁.to rb _ sndₚ₁)

Raw&ₚ : {A B : @0 List Σ → Set} → (ra : Raw A) (rb : Raw B) → Raw (&ₚ A B)
Raw.D  (Raw&ₚ ra rb) = (Raw.D ra) × (Raw.D rb)
Raw.to (Raw&ₚ ra rb) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = (Raw.to ra fstₚ₁) , (Raw.to rb sndₚ₁)
