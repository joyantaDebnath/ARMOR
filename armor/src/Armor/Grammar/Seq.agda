import      Armor.Grammar.Seq.MaximalParser
import      Armor.Grammar.Seq.Parser
import      Armor.Grammar.Seq.Properties
import      Armor.Grammar.Seq.TCB
open import Armor.Prelude

module Armor.Grammar.Seq (Σ : Set) where

open Armor.Grammar.Seq.Parser Σ public
open Armor.Grammar.Seq.TCB    Σ public

module Seq where
  open import Armor.Grammar.Seq.Properties Σ public

  module MaximalParser where
    open Armor.Grammar.Seq.MaximalParser Σ public
