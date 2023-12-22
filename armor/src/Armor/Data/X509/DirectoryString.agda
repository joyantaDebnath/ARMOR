import Armor.Data.X509.DirectoryString.Eq
import Armor.Data.X509.DirectoryString.Parser
import Armor.Data.X509.DirectoryString.Properties
import Armor.Data.X509.DirectoryString.TCB

module Armor.Data.X509.DirectoryString where

open Armor.Data.X509.DirectoryString.Parser public
open Armor.Data.X509.DirectoryString.TCB public
  hiding (module DirectoryString)

module DirectoryString where
  open Armor.Data.X509.DirectoryString.Eq         public
  open Armor.Data.X509.DirectoryString.Properties public
