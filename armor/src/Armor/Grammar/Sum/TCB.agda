open import Armor.Prelude
import      Armor.Grammar.Definitions.NonMalleable

module Armor.Grammar.Sum.TCB (Σ : Set) where

open Armor.Grammar.Definitions.NonMalleable Σ

data Sum (A B : @0 List Σ → Set) (@0 xs : List Σ) : Set where
  inj₁ : A xs → Sum A B xs
  inj₂ : B xs → Sum A B xs

RawSum : {A B : @0 List Σ → Set} → Raw A → Raw B → Raw (Sum A B)
Raw.D (RawSum A B) = (Raw.D A) ⊎ (Raw.D B)
Raw.to (RawSum A B) (inj₁ x) = inj₁ (Raw.to A x)
Raw.to (RawSum A B) (inj₂ x) = inj₂ (Raw.to B x)
