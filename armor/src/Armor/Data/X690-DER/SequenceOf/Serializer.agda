open import Armor.Binary
open import Armor.Data.X690-DER.SequenceOf.TCB
open import Armor.Grammar.IList
open import Armor.Grammar.Parallel
open import Armor.Prelude

open Armor.Grammar.Parallel UInt8

module Armor.Data.X690-DER.SequenceOf.Serializer
  {A : @0 List UInt8 → Set} (ser : ∀ {@0 bs} → A bs → Singleton bs)
  where

serializeSequenceOf
  : ∀ {@0 bs} → SequenceOf A bs → Singleton bs
serializeSequenceOf nil = self
serializeSequenceOf {bs} (cons (mkIListCons{bs₁}{bs₂} head₁ tail₁ bs≡))
  with ser head₁
  |    serializeSequenceOf tail₁
... | singleton h h≡ | singleton t t≡ =
  singleton (h ++ t)
    (begin h ++ t ≡⟨ cong₂ _++_ h≡ t≡ ⟩
           bs₁ ++ bs₂ ≡⟨ sym bs≡ ⟩
           bs ∎)
  where open ≡-Reasoning

serializeNonEmptySequenceOf
  : ∀ {@0 bs} → NonEmptySequenceOf A bs → Singleton bs
serializeNonEmptySequenceOf (mk×ₚ fstₚ sndₚ) = serializeSequenceOf fstₚ
