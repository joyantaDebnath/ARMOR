import      Armor.Grammar.IList.TCB
import      Armor.Grammar.Serializer
open import Armor.Prelude

module Armor.Grammar.IList.Serializer (Σ : Set) where

open Armor.Grammar.IList.TCB  Σ
open Armor.Grammar.Serializer Σ

serializeIList : ∀ {A : @0 List Σ → Set} → Serializer A → Serializer (IList A)
serializeIList s nil = self
serializeIList s (consIList{bs₁}{bs₂} head tail bs≡) =
  let tl@(singleton t t≡) = serializeIList s tail
  in
  singleton ((↑ s head) ++ t)
    (begin ↑ s head ++ t ≡⟨ cong₂ _++_ (Singleton.x≡ (s head)) t≡ ⟩
           bs₁ ++ bs₂ ≡⟨ sym bs≡ ⟩
           _ ∎)
  where open ≡-Reasoning
