open import Armor.Binary
open import Armor.Data.X690-DER.Null.TCB
import      Armor.Data.X690-DER.TLV.Properties as TLV
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
open import Armor.Prelude
import      Data.Nat.Properties     as Nat

module Armor.Data.X690-DER.Null.Properties where

open Armor.Grammar.Definitions              UInt8

@0 unambiguous : Unambiguous Null
unambiguous = TLV.unambiguous λ where (─ refl) (─ refl) → refl

@0 nonmalleable : NonMalleable RawNull
nonmalleable = TLV.nonmalleable{t = Tag.Null} (subsingleton⇒nonmalleable (λ where (─ _ , (─ refl)) (─ _ , (─ refl)) → refl))

instance
  eq≋ : Eq≋ (λ x → Erased (x ≡ []))
  Eq≋._≋?_ eq≋ (─ refl) (─ refl) = yes ≋-refl
