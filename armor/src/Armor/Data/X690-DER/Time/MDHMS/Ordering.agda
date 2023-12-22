open import Armor.Binary
open import Armor.Data.X690-DER.Time.Day
open import Armor.Data.X690-DER.Time.Hour
open import Armor.Data.X690-DER.Time.MDHMS.Properties
open import Armor.Data.X690-DER.Time.MDHMS.TCB
open import Armor.Data.X690-DER.Time.Minute
open import Armor.Data.X690-DER.Time.MDHMS.TCB
open import Armor.Data.X690-DER.Time.Month
open import Armor.Data.X690-DER.Time.TimeType
open import Armor.Data.X690-DER.Time.Sec
import      Armor.Grammar.Definitions
open import Armor.Prelude
open import Data.Nat.Properties
open import Data.Product.Relation.Binary.Lex.Strict
open import Data.Product.Relation.Binary.Pointwise.NonDependent
  hiding (×-transitive ; ×-respects₂)
open import Relation.Binary.Definitions
open import Relation.Binary.Structures

module Armor.Data.X690-DER.Time.MDHMS.Ordering where

open Armor.Grammar.Definitions UInt8

trans-MDHMS<' : Transitive _MDHMS<'_
trans-MDHMS<' =
  ×-transitive{_<₂_ = (×-Lex _≡_ _<_ (×-Lex _≡_ _<_ _<_))}
    (×-isEquivalence{_≈₁_ = _≡_} isEquivalence isEquivalence)
    (×-respects₂ isEquivalence <-resp₂-≡ <-resp₂-≡)
    (×-transitive{_<₁_ = _<_}{_<₂_ = _<_} isEquivalence <-resp₂-≡ <-trans <-trans)
    (×-transitive{_<₂_ = ×-Lex _≡_ _<_ _<_}
      isEquivalence <-resp₂-≡ <-trans
      (×-transitive{_<₁_ = _<_}{_<₂_ = _<_} isEquivalence <-resp₂-≡ <-trans <-trans))

private
  compare-MDHMS<“ : Trichotomous (Pointwise (Pointwise _≡_ _≡_) (Pointwise _≡_ (Pointwise _≡_ _≡_))) _MDHMS<'_
  compare-MDHMS<“ =
    ×-compare{_≈₁_ = Pointwise _≡_ _≡_} (×-symmetric{_∼₁_ = _≡_}{_∼₂_ = _≡_} sym sym)
      (×-compare sym <-cmp <-cmp)
      (×-compare sym <-cmp
      (×-compare sym <-cmp <-cmp))

compare-MDHMS<' : Trichotomous _≡_ _MDHMS<'_
compare-MDHMS<' x y =
  case compare-MDHMS<“ x y ret (const _) of λ where
    (tri< a ¬b ¬c) → tri< a (λ where refl → contradiction ((refl , refl) , (refl , (refl , refl))) ¬b) ¬c
    (tri≈ ¬a ((refl , refl) , (refl , (refl , refl))) ¬c) → tri≈ ¬a refl ¬c
    (tri> ¬a ¬b c) → tri> ¬a (λ where refl → contradiction ((refl , refl) , (refl , (refl , refl))) ¬b) c

isStrictTotalOrder : IsStrictTotalOrder _≡_ _MDHMS<'_
IsStrictTotalOrder.isEquivalence isStrictTotalOrder = isEquivalence
IsStrictTotalOrder.trans isStrictTotalOrder = trans-MDHMS<'
IsStrictTotalOrder.compare isStrictTotalOrder = compare-MDHMS<'

compare-MDHMS< : ∀ {@0 bs₁ bs₂} → (m₁ : MDHMS bs₁) (m₂ : MDHMS bs₂) → Tri (m₁ MDHMS< m₂) (_≋_{A = MDHMS} m₁ m₂) (m₂ MDHMS< m₁)
compare-MDHMS< m₁ m₂ = case compare-MDHMS<' (Raw.to RawMDHMS m₁) (Raw.to RawMDHMS m₂) ret (const _) of λ where
  (tri< a ¬b ¬c) → tri< a (λ where ≋-refl → contradiction refl ¬b) ¬c
  (tri≈ ¬a refl ¬c) → tri≈ ¬a (case ‼ nonmalleable m₁ m₂ refl ret (const _) of λ where refl → ≋-refl) ¬c
  (tri> ¬a ¬b c) → tri> ¬a (λ where ≋-refl → contradiction refl ¬b) c

_MDHMS≤?_ : ∀ {@0 bs₁ bs₂} → (m₁ : MDHMS bs₁) (m₂ : MDHMS bs₂) → Dec (m₁ MDHMS≤ m₂)
m₁ MDHMS≤? m₂ = case compare-MDHMS< m₁ m₂ ret (const _) of λ where
  (tri< a ¬b ¬c) → yes (inj₂ a)
  (tri≈ ¬a b ¬c) → yes (inj₁ b)
  (tri> ¬a ¬b c) → no λ where
    (inj₁ x) → contradiction x ¬b
    (inj₂ y) → contradiction y ¬a

