open import Armor.Binary
open import Armor.Prelude
open import Armor.Data.X690-DER.Time.TimeType.TCB
import      Armor.Grammar.Definitions

module Armor.Data.X690-DER.Time.TimeType.Relation where

open Armor.Grammar.Definitions UInt8

Lift : ∀ {ℓ} (_∼_ : ℕ → ℕ → Set ℓ) → ∀ {@0 size l u bs₁ bs₂} → TimeType size l u bs₁ → TimeType size l u bs₂ → Set ℓ
Lift _∼_ t₁ t₂ = TimeType.getTime t₁ ∼ TimeType.getTime t₂

infix 4 _Time≤_ _Time≥_ _Time<_ _Time>_ _Time≡_

_Time≤_ = Lift _≤_
_Time≥_ = Lift _≥_
_Time<_ = Lift _<_
_Time>_ = Lift _>_
_Time≡_ = Lift _≡_

liftDec
  : ∀ {ℓ} (_∼_ : ℕ → ℕ → Set ℓ) → (∀ x y → Dec (x ∼ y))
    → ∀ {@0 size l u bs₁ bs₂} → (t₁ : TimeType size l u bs₁) → (t₂ : TimeType size l u bs₂)
    → Dec (Lift _∼_ t₁ t₂)
liftDec _∼_ d t₁ t₂ = d (TimeType.getTime t₁) (TimeType.getTime t₂)

_Time≤?_ = liftDec _≤_ _≤?_
_Time≟_ = liftDec _≡_ _≟_

Time≡⇒≡ : ∀ {@0 size l u bs₁ bs₂} {t₁ : TimeType size l u bs₁} {t₂ : TimeType size l u bs₂}
          → t₁ Time≡ t₂ → _≋_{A = TimeType size l u} t₁ t₂
Time≡⇒≡{bs₁ = bs₁}{bs₂}{t₁ = t₁}{t₂} time≡
  with ‼ UInt8.asciiNum-injective bs₁ bs₂
           (toWitness (TimeType.charset t₁)) (toWitness (TimeType.charset t₂))
           (trans (TimeType.bsLen t₁) (sym (TimeType.bsLen t₂)))
           (asciiNum bs₁ ≡⟨ sym $ Singleton.x≡ (TimeType.time t₁) ⟩
           TimeType.getTime t₁ ≡⟨ time≡ ⟩
           TimeType.getTime t₂ ≡⟨ Singleton.x≡ (TimeType.time t₂) ⟩
           asciiNum bs₂ ∎)
  where
  open ≡-Reasoning
Time≡⇒≡{l = l}{u}{bs₁}{t₁ = t₁}{t₂} _ | refl
  with ‼ T-unique{⌊ All.all? (inRange? '0' '9') bs₁ ⌋} (TimeType.charset t₁) (TimeType.charset t₂)
  |    ‼ ≡-unique (TimeType.bsLen t₁) (TimeType.bsLen t₂)
  |    ‼ uniqueSingleton (TimeType.time t₁) (TimeType.time t₂)
... | refl | refl | refl
  with ‼ inRange-unique{A = ℕ}{B = ℕ} (TimeType.range t₁) (TimeType.range t₂)
... | refl = ≋-refl
