open import Armor.Prelude
import      Armor.Grammar.Serializer
import      Armor.Grammar.Sum.TCB

module Armor.Grammar.Sum.Serializer (Σ : Set) where

open Armor.Grammar.Sum.TCB    Σ
open Armor.Grammar.Serializer Σ

serialize : ∀ {A B : @0 List Σ → Set}
            → Serializer A → Serializer B
            → Serializer (Sum A B)
serialize sa sb (inj₁ x) = sa x
serialize sa sb (inj₂ x) = sb x
