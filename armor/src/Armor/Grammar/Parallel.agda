import      Armor.Grammar.Parallel.Parser
import      Armor.Grammar.Parallel.Properties
import      Armor.Grammar.Parallel.TCB

module Armor.Grammar.Parallel (Σ : Set) where

open Armor.Grammar.Parallel.Parser Σ public
open Armor.Grammar.Parallel.TCB    Σ public

module Parallel where
  open import Armor.Grammar.Parallel.Properties Σ public
