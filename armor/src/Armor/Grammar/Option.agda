import      Armor.Grammar.Serializer
import      Armor.Grammar.Option.Parser
import      Armor.Grammar.Option.Properties
import      Armor.Grammar.Option.TCB
open import Armor.Prelude

module Armor.Grammar.Option (Σ : Set) where

open Armor.Grammar.Serializer  Σ

open Armor.Grammar.Option.TCB Σ
  public
  hiding (module Option)

module Option where
  open import Armor.Grammar.Option.Parser Σ public
  open import Armor.Grammar.Option.Properties Σ public

  serialize : ∀ {@0 A} → Serializer A → Serializer (Option A)
  serialize s none = self
  serialize s (some x) = s x
