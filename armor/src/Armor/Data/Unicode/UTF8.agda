import Armor.Data.Unicode.UTF8.Parser
import Armor.Data.Unicode.UTF8.Properties
import Armor.Data.Unicode.UTF8.Serializer
import Armor.Data.Unicode.UTF8.TCB

module Armor.Data.Unicode.UTF8 where

open Armor.Data.Unicode.UTF8.Parser public
open Armor.Data.Unicode.UTF8.TCB    public
  hiding (module UTF8)

module UTF8 where
  open Armor.Data.Unicode.UTF8.Properties public
  open Armor.Data.Unicode.UTF8.Serializer public
  open Armor.Data.Unicode.UTF8.TCB.UTF8   public
