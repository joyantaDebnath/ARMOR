import Armor.Data.X509.GeneralNames.GeneralName.Eq
import Armor.Data.X509.GeneralNames.GeneralName.Parser
import Armor.Data.X509.GeneralNames.GeneralName.Properties
import Armor.Data.X509.GeneralNames.GeneralName.TCB

module Armor.Data.X509.GeneralNames.GeneralName where

open Armor.Data.X509.GeneralNames.GeneralName.Parser public
open Armor.Data.X509.GeneralNames.GeneralName.TCB    public
  hiding (module GeneralName)

module GeneralName where
  open Armor.Data.X509.GeneralNames.GeneralName.Properties public
  open Armor.Data.X509.GeneralNames.GeneralName.Eq public

