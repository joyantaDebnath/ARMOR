open import Armor.Binary
open import Armor.Data.X690-DER.Default.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Prelude

module Armor.Data.X690-DER.Default.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

module _ {A : @0 List UInt8 → Set} ⦃ _ : Eq≋ A ⦄ {@0 bs' : List UInt8} (default : A bs') where

  @0 uniqueNotDefault : ∀ {bs} → (o : Option A bs) → Unique (NotDefault default o)
  uniqueNotDefault none = ⊤-unique
  uniqueNotDefault (some x) = T-unique

  notDefault? : ∀ {@0 bs} → (o : Option A bs) → Dec (NotDefault default o)
  notDefault? none = yes tt
  notDefault? (some a) = T-dec

  @0 unambiguous : Unambiguous A → NonEmpty A → Unambiguous (Default A default)
  unambiguous ua ne (mkDefault none tt) (mkDefault none tt) = refl
  unambiguous ua ne (mkDefault none tt) (mkDefault (some v₂) nd₂) =
    contradiction refl (ne v₂)
  unambiguous ua ne (mkDefault (some v₁) nd₁) (mkDefault none nd₂) =
    contradiction refl (ne v₁)
  unambiguous ua ne (mkDefault (some v₁) nd₁) (mkDefault (some v₂) nd₂) =
    case ua v₁ v₂ of λ where
      refl → case (‼ T-unique nd₁ nd₂) ret (const _) of λ where
        refl → refl

  @0 nonmalleable : {R : Raw A} → NonMalleable R → NonMalleable (RawDefault R default)
  nonmalleable nm (mkDefault none nd₁) (mkDefault none nd₂) eq =
    case (‼ T-unique nd₁ nd₂) ret (const _) of λ where
      refl → refl
  nonmalleable nm (mkDefault none nd₁) (mkDefault (some v₂) nd₂) eq =
    contradiction
      (case (nm default v₂ eq) of λ where
        refl → ≋-refl)
      (toWitnessFalse nd₂)
  nonmalleable nm (mkDefault (some v₁) nd₁) (mkDefault none nd₂) eq =
    contradiction
      (case (nm v₁ default eq) of λ where
        refl → ≋-refl)
      (toWitnessFalse nd₁)
  nonmalleable nm (mkDefault (some v₁) nd₁) (mkDefault (some v₂) nd₂) eq =
    case nm v₁ v₂ eq ret (const _) of λ where
      refl → case (‼ T-unique nd₁ nd₂) ret (const _) of λ where
        refl → refl

  eq≋ : Eq≋ (Default A default)
  Eq≋._≋?_ eq≋ d₁@(mkDefault a₁ nd₁) d₂@(mkDefault a₂ nd₂) =
    case a₁ ≋? a₂ ret (const _) of λ where
      (no ¬p) → no λ where ≋-refl → contradiction ≋-refl ¬p
      (yes ≋-refl) → yes (case (singleton a₁ refl) ret (const _) of λ where
        (singleton none refl) → case ‼ ⊤-unique nd₁ nd₂ ret (const _) of λ where
          refl → ≋-refl
        (singleton (some x) refl) → case ‼ T-unique nd₁ nd₂ ret (const _) of λ where
          refl → ≋-refl )
