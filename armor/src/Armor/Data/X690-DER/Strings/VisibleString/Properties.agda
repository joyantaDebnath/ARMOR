open import Armor.Binary
open import Armor.Data.X690-DER.Strings.VisibleString.TCB
import      Armor.Data.X690-DER.TLV.Properties as TLV
import      Armor.Grammar.Definitions
open import Armor.Prelude

module Armor.Data.X690-DER.Strings.VisibleString.Properties where

open Armor.Grammar.Definitions                   UInt8
open VisibleStringValue using (size)

@0 unambiguous : Unambiguous VisibleStringValue
unambiguous (mkVisibleStringValue chars range refl) (mkVisibleStringValue .chars range₁ refl) =
  case All.irrelevant (inRange-unique{A = ℕ}{B = UInt8}) range range₁ of λ where
    refl → refl

sizeUnique : ∀ {@0 bs} → (a₁ a₂ : VisibleStringValue bs) → size a₁ ≡ size a₂
sizeUnique (mkVisibleStringValue chars range refl) (mkVisibleStringValue .chars range₁ refl) = refl

instance
  VisibleStringEq : Eq (Exists─ (List UInt8) VisibleStringValue)
  Eq._≟_ VisibleStringEq (─ ._ , mkVisibleStringValue chars₁ range₁ refl) (─ ._ , mkVisibleStringValue chars₂ range₂ refl) =
    case chars₁ ≟ chars₂ of λ where
      (no ¬p) → no λ where refl → contradiction refl ¬p
      (yes refl) →
        case ‼ All.irrelevant{P = InRange{A = ℕ}{B = UInt8} 32 127} (inRange-unique{A = ℕ}{B = UInt8}) range₁ range₂
        ret (const _)
        of λ where
          refl → yes refl

@0 nonmalleableValue : NonMalleable RawVisibleStringValue
nonmalleableValue (mkVisibleStringValue chars range refl) (mkVisibleStringValue chars₁ range₁ refl) refl =
  case All.irrelevant (inRange-unique{A = ℕ}{B = UInt8}) range range₁ of λ where
    refl → refl

@0 nonmalleable : NonMalleable RawVisibleString
nonmalleable = TLV.nonmalleable nonmalleableValue
