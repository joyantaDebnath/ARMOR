open import Armor.Prelude
import Armor.Grammar.Parser.Lit
import Armor.Grammar.Parser.Maximal
import Armor.Grammar.Parser.WellFounded
import Armor.Grammar.Parser.While

module Armor.Grammar.Parser (Σ : Set) where

open import Armor.Grammar.Parser.Core Σ public

open Armor.Grammar.Parser.Lit         Σ public
open Armor.Grammar.Parser.Maximal     Σ public
open Armor.Grammar.Parser.WellFounded Σ public
open Armor.Grammar.Parser.While       Σ public

