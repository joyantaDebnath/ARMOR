import Armor.Data.X509.GeneralNames.Eq
import Armor.Data.X509.GeneralNames.Parser
import Armor.Data.X509.GeneralNames.Properties
import Armor.Data.X509.GeneralNames.TCB
import Armor.Data.X509.GeneralNames.GeneralName

module Armor.Data.X509.GeneralNames where

open Armor.Data.X509.GeneralNames.Parser public
open Armor.Data.X509.GeneralNames.TCB public

module GeneralNames where
  open Armor.Data.X509.GeneralNames.Eq public
  open Armor.Data.X509.GeneralNames.Properties public
  open Armor.Data.X509.GeneralNames.GeneralName public

