import      Armor.Grammar.Definitions.Eq
import      Armor.Grammar.Definitions.Iso
import      Armor.Grammar.Definitions.NoConfusion
import      Armor.Grammar.Definitions.NoOverlap
import      Armor.Grammar.Definitions.NoSubstrings
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.Definitions.NonEmpty
import      Armor.Grammar.Definitions.Unambiguous
open import Armor.Prelude

module Armor.Grammar.Definitions (Σ : Set) where

open Armor.Grammar.Definitions.Eq           Σ public
open Armor.Grammar.Definitions.Iso          Σ public
open Armor.Grammar.Definitions.NoOverlap    Σ public
open Armor.Grammar.Definitions.NoConfusion  Σ public
open Armor.Grammar.Definitions.NoSubstrings Σ public
open Armor.Grammar.Definitions.NonEmpty     Σ public
open Armor.Grammar.Definitions.NonMalleable Σ public
open Armor.Grammar.Definitions.Unambiguous  Σ public
