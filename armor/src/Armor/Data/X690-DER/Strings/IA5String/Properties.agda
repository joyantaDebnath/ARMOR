open import Armor.Binary
open import Armor.Data.X690-DER.Strings.IA5String.TCB
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.TLV as TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
open import Armor.Data.X690-DER.OctetString
open import Armor.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Armor.Data.X690-DER.Strings.IA5String.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Data.X690-DER.Strings.IA5String.TCB.IA5StringValue
  using (size)

@0 unambiguous : Unambiguous IA5StringValue
unambiguous (mkIA5StringValue self all<128) (mkIA5StringValue self all<129) =
  subst₀ (λ x → _ ≡ mkIA5StringValue self x)
    (T-unique all<128 all<129) refl

sizeUnique : ∀ {@0 bs} → (a₁ a₂ : IA5StringValue bs) → size a₁ ≡ size a₂
sizeUnique (mkIA5StringValue self all<128) (mkIA5StringValue self all<129) = refl

Rep : @0 List UInt8 → Set
Rep = Σₚ OctetStringValue λ _ str → Erased (True (All.all? (Fin._<? (# 128)) (↑ str)))

equiv : Equivalent Rep IA5StringValue
proj₁ equiv (mk×ₚ fstₚ₁ (─ sndₚ₁)) = mkIA5StringValue fstₚ₁ sndₚ₁
proj₂ equiv (mkIA5StringValue str all<128) = mk×ₚ str (─ all<128)

iso   : Iso Rep IA5StringValue
proj₁ iso = equiv
proj₁ (proj₂ iso) (mk×ₚ fstₚ₁ sndₚ₁) = refl
proj₂ (proj₂ iso) (mkIA5StringValue str all<128) = refl

instance
  IA5StringEq : Eq (Exists─ _ IA5StringValue)
  IA5StringEq =
    Iso.isoEq iso
      (Parallel.eqΣₚ it
        λ a →
          record
            { _≟_ = λ where
              (─ x) (─ y) → yes (cong (λ x → ─ x) (‼ T-unique x y))
            })

  IA5StringEq≋ : Eq≋ IA5StringValue
  IA5StringEq≋ = Eq⇒Eq≋ it

@0 nonmalleableValue : NonMalleable RawIA5StringValue
nonmalleableValue (mkIA5StringValue self all<128) (mkIA5StringValue self all<129) refl = 
  case (‼ T-unique all<128 all<129) of λ where
    refl → ‼ refl

@0 nonmalleable : NonMalleable RawIA5String
nonmalleable = TLV.nonmalleable nonmalleableValue
