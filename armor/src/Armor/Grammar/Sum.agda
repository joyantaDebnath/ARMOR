open import Armor.Prelude
import      Armor.Grammar.Sum.Parser
import      Armor.Grammar.Sum.Properties
import      Armor.Grammar.Sum.Serializer
import      Armor.Grammar.Sum.TCB

module Armor.Grammar.Sum (Σ : Set) where

open Armor.Grammar.Sum.TCB    Σ public
  hiding (module Sum)
open Armor.Grammar.Sum.Parser Σ public

module Sum where
  open Armor.Grammar.Sum.Properties Σ public
  open Armor.Grammar.Sum.Serializer Σ public
  open Armor.Grammar.Sum.TCB        Σ public
    using (inj₁ ; inj₂)
