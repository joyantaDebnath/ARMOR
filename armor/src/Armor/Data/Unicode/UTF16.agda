import Armor.Data.Unicode.UTF16.Parser
import Armor.Data.Unicode.UTF16.Properties
import Armor.Data.Unicode.UTF16.TCB

module Armor.Data.Unicode.UTF16 where

open Armor.Data.Unicode.UTF16.TCB    public
  hiding (size)
open Armor.Data.Unicode.UTF16.Parser public

module UTF16 where
  open Armor.Data.Unicode.UTF16.Properties public
  open Armor.Data.Unicode.UTF16.TCB        public
    using (size)
