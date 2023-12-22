import Armor.Data.Unicode.Properties
import Armor.Data.Unicode.TCB
import Armor.Data.Unicode.UTF8
import Armor.Data.Unicode.UTF16
import Armor.Data.Unicode.UTF32

module Armor.Data.Unicode where

open Armor.Data.Unicode.TCB public
  hiding (module Unicode)
open Armor.Data.Unicode.UTF8 public
open Armor.Data.Unicode.UTF16 public
open Armor.Data.Unicode.UTF32 public

module Unicode where
  open Armor.Data.Unicode.Properties public
