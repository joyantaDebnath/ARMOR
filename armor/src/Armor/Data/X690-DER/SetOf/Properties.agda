open import Armor.Binary
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.SetOf.Order.TCB
open import Armor.Data.X690-DER.SetOf.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
open import Armor.Prelude

module Armor.Data.X690-DER.SetOf.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8

@0 unambiguousFields
  : {A : @0 List UInt8 → Set} → Unambiguous A → NonEmpty A → NoSubstrings A
    → Unambiguous (SetOfFields A)
unambiguousFields ua ne ns (mkSetOfFields elems order) (mkSetOfFields elems₁ order₁) =
  case SequenceOf.Bounded.unambiguous{n = 1} ua ne ns elems elems₁ of λ where
    refl → case ‼ T-unique order order₁ ret (λ _ → _ ≡ _) of λ where
      refl → refl

@0 unambiguous
  : {A : @0 List UInt8 → Set} → Unambiguous A → NonEmpty A → NoSubstrings A
    → Unambiguous (SetOf A)
unambiguous ua ne ns = TLV.unambiguous (unambiguousFields ua ne ns)

@0 nonmalleableFields
  : {A : @0 List UInt8 → Set} {R : Raw A}
    → NonEmpty A → NoSubstrings A
    → NonMalleable R → NonMalleable (RawSetOfFields R)
nonmalleableFields ne ns nm (mkSetOfFields elems order) (mkSetOfFields elems₁ order₁) eq =
  case SequenceOf.Bounded.nonmalleable ne ns nm elems elems₁ eq of λ where
    refl → case (‼ T-unique order order₁) ret (λ _ → _ ≡ _) of λ where
      refl → refl

@0 nonmalleable
  : {A : @0 List UInt8 → Set} {R : Raw A}
    → NonEmpty A → NoSubstrings A
    → NonMalleable R → NonMalleable (RawSetOf R)
nonmalleable ne ns nm = TLV.nonmalleable (nonmalleableFields ne ns nm)

instance
  eq≋ : {A : @0 List UInt8 → Set} ⦃ _ : Eq≋ A ⦄ → Eq≋ (SetOfFields A)
  Eq≋._≋?_ eq≋ (mkSetOfFields (mk×ₚ elems₁ elems₁Len) order₁) (mkSetOfFields (mk×ₚ elems₂ elems₂Len) order₂) =
    case _≋?_ ⦃ SequenceOf.SequenceOfEq≋ ⦄ elems₁ elems₂ of λ where
      (no ¬p) → no λ where ≋-refl → contradiction ≋-refl ¬p
      (yes ≋-refl) →
        case _,′_{A = elems₁Len ≡ elems₂Len}{B = Erased (order₁ ≡ order₂)} (erased-unique ≤-unique elems₁Len elems₂Len) (─ (T-unique order₁ order₂)) of λ where
        (refl , ─ refl) → yes ≋-refl
