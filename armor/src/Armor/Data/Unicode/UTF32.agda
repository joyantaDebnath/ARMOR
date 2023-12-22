import Armor.Data.Unicode.UTF32.Parser
import Armor.Data.Unicode.UTF32.Properties
import Armor.Data.Unicode.UTF32.TCB

module Armor.Data.Unicode.UTF32 where

open Armor.Data.Unicode.UTF32.TCB    public

module UTF32 where
  open Armor.Data.Unicode.UTF32.Properties public
  open Armor.Data.Unicode.UTF32.Parser public
