import Armor.Data.X509.Extension.AIA.AccessDesc
import Armor.Data.X509.Extension.AIA.Parser
import Armor.Data.X509.Extension.AIA.TCB
import Armor.Data.X509.Extension.AIA.Properties

module Armor.Data.X509.Extension.AIA where

open Armor.Data.X509.Extension.AIA.Parser public
open Armor.Data.X509.Extension.AIA.TCB    public

module AIA where
  open Armor.Data.X509.Extension.AIA.AccessDesc public
  open Armor.Data.X509.Extension.AIA.Properties public
