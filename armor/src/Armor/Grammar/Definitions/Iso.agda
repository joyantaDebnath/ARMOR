import Armor.Grammar.Definitions.Iso.Base
import Armor.Grammar.Definitions.Iso.Properties

module Armor.Grammar.Definitions.Iso (Σ : Set) where

open Armor.Grammar.Definitions.Iso.Base Σ public

module Iso where
  open Armor.Grammar.Definitions.Iso.Properties Σ public
