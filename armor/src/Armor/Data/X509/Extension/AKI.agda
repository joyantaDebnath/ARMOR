import Armor.Data.X509.Extension.AKI.Eq
import Armor.Data.X509.Extension.AKI.Parser
import Armor.Data.X509.Extension.AKI.Properties
import Armor.Data.X509.Extension.AKI.TCB

module Armor.Data.X509.Extension.AKI where

open Armor.Data.X509.Extension.AKI.Parser public
open Armor.Data.X509.Extension.AKI.TCB    public

module AKI where
  open Armor.Data.X509.Extension.AKI.Eq          public
  open Armor.Data.X509.Extension.AKI.Properties  public
