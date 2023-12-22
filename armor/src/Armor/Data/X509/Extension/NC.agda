import Armor.Data.X509.Extension.NC.Eq
import Armor.Data.X509.Extension.NC.GeneralSubtree
import Armor.Data.X509.Extension.NC.Parser
import Armor.Data.X509.Extension.NC.Properties
import Armor.Data.X509.Extension.NC.TCB

module Armor.Data.X509.Extension.NC where

open Armor.Data.X509.Extension.NC.Parser public
open Armor.Data.X509.Extension.NC.TCB    public

module NC where
  open Armor.Data.X509.Extension.NC.Eq         public
  open Armor.Data.X509.Extension.NC.Properties public
