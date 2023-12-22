import Armor.Data.X509.DisplayText.Parser
import Armor.Data.X509.DisplayText.Properties
import Armor.Data.X509.DisplayText.TCB

module Armor.Data.X509.DisplayText where

open Armor.Data.X509.DisplayText.Parser public
open Armor.Data.X509.DisplayText.TCB public
  hiding (module DisplayText ; equivalent)

module DisplayText where
  open Armor.Data.X509.DisplayText.Properties public
  open Armor.Data.X509.DisplayText.TCB public
    using (equivalent)
