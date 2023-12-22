open import Armor.Binary
open import Armor.Data.X690-DER.Time.GeneralizedTime.Properties
open import Armor.Data.X690-DER.Time.GeneralizedTime.TCB
open import Armor.Data.X690-DER.Time.MDHMS
open import Armor.Data.X690-DER.Time.TimeType
open import Armor.Data.X690-DER.Time.Year
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
open import Armor.Prelude
open import Data.Product.Relation.Binary.Pointwise.NonDependent
  hiding (×-transitive ; ×-respects₂)
open import Data.Nat.Properties
open import Data.Product.Relation.Binary.Lex.Strict
open import Relation.Binary.Definitions
open import Relation.Binary.Structures

module Armor.Data.X690-DER.Time.GeneralizedTime.Ordering where

open Armor.Grammar.Definitions UInt8

trans-GeneralizedTimeFields<' : Transitive _GeneralizedTimeFields<'_
trans-GeneralizedTimeFields<' =
  ×-transitive{B = ⊤}
    {_≈₁_ = Pointwise _≡_ _≡_}{_<₁_ = ×-Lex _≡_ _<_ MDHMS._<'_}{_<₂_ = λ _ _ → ⊥}
    (×-isEquivalence isEquivalence isEquivalence)
    (×-respects₂{_<₁_ = _<_}{_<₂_ = MDHMS._<'_} isEquivalence <-resp₂-≡ (resp₂ MDHMS._<'_))
    (×-transitive{_≈₁_ = _≡_}{_<₁_ = _<_}{_<₂_ = MDHMS._<'_}
      isEquivalence <-resp₂-≡ <-trans MDHMS.trans<')
    λ ()

private
  compare-GeneralizedTimeFields<“ : Trichotomous (Pointwise (Pointwise _≡_ _≡_) _≡_) _GeneralizedTimeFields<'_
  compare-GeneralizedTimeFields<“ =
    ×-compare{_≈₁_ = Pointwise _≡_ _≡_}{_≈₂_ = _≡_}
      (×-symmetric{_∼₁_ = _≡_}{_∼₂_ = _≡_} sym sym)
      (×-compare {_≈₁_ = _≡_} {_≈₂_ = _≡_} sym <-cmp MDHMS.compare-MDHMS<')
      λ where tt tt → tri≈ (λ ()) refl (λ ())

compare-GeneralizedTimeFields<' : Trichotomous _≡_ _GeneralizedTimeFields<'_
compare-GeneralizedTimeFields<' x y =
  case compare-GeneralizedTimeFields<“ x y ret (const _) of λ where
    (tri< a ¬b ¬c) → tri< a (λ where refl → contradiction ((refl , refl) , refl) ¬b) ¬c
    (tri≈ ¬a ((refl , refl) , refl) ¬c) → tri≈ ¬a refl ¬c
    (tri> ¬a ¬b c) → tri> ¬a (λ where refl → contradiction ((refl , refl) , refl) ¬b) c

isStrictTotalOrder : IsStrictTotalOrder _≡_ _GeneralizedTimeFields<'_
IsStrictTotalOrder.isEquivalence isStrictTotalOrder = isEquivalence
IsStrictTotalOrder.trans isStrictTotalOrder = trans-GeneralizedTimeFields<'
IsStrictTotalOrder.compare isStrictTotalOrder = compare-GeneralizedTimeFields<'

compare-GeneralizedTimeFields<
  : ∀ {@0 bs₁ bs₂} → (g₁ : GeneralizedTimeFields bs₁) (g₂ : GeneralizedTimeFields bs₂)
    → Tri (g₁ GeneralizedTimeFields< g₂) (_≋_{A = GeneralizedTimeFields} g₁ g₂) (g₂ GeneralizedTimeFields< g₁)
compare-GeneralizedTimeFields< g₁ g₂ =
  case compare-GeneralizedTimeFields<' (Raw.to RawGeneralizedTimeFields g₁) (Raw.to RawGeneralizedTimeFields g₂) ret (const _) of λ where
    (tri< a ¬b ¬c) → tri< a (λ where ≋-refl → contradiction refl ¬b) ¬c
    (tri≈ ¬a b ¬c) →
      tri≈ ¬a (case ‼ nonmalleableFields g₁ g₂ b ret (const _) of λ where refl → ≋-refl) ¬c
    (tri> ¬a ¬b c) → tri> ¬a (λ where ≋-refl → contradiction refl ¬b) c

_GeneralizedTimeFields≤?_
  : ∀ {@0 bs₁ bs₂} → (g₁ : GeneralizedTimeFields bs₁) (g₂ : GeneralizedTimeFields bs₂)
    → Dec (g₁ GeneralizedTimeFields≤ g₂)
g₁ GeneralizedTimeFields≤? g₂ =
  case compare-GeneralizedTimeFields< g₁ g₂ ret (const _) of λ where
    (tri< a ¬b ¬c) → yes (inj₂ a)
    (tri≈ ¬a b ¬c) → yes (inj₁ b)
    (tri> ¬a ¬b c) → no (λ where
      (inj₁ x) → contradiction x ¬b
      (inj₂ z) → contradiction z ¬a)
