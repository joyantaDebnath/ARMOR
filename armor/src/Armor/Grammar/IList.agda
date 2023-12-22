import Armor.Grammar.IList.All
import Armor.Grammar.IList.Parser
import Armor.Grammar.IList.Properties
import Armor.Grammar.IList.Serializer
import Armor.Grammar.IList.TCB

module Armor.Grammar.IList (Σ : Set) where

module IList where
  open Armor.Grammar.IList.All        Σ public
  open Armor.Grammar.IList.Properties Σ public
  open Armor.Grammar.IList.TCB.IList  Σ public

open Armor.Grammar.IList.Parser       Σ public
open Armor.Grammar.IList.Serializer   Σ public
open Armor.Grammar.IList.TCB          Σ public
  hiding (module IList)
