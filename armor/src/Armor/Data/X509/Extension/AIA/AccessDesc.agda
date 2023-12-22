import Armor.Data.X509.Extension.AIA.AccessDesc.Eq
import Armor.Data.X509.Extension.AIA.AccessDesc.Parser
import Armor.Data.X509.Extension.AIA.AccessDesc.Properties
import Armor.Data.X509.Extension.AIA.AccessDesc.TCB

module Armor.Data.X509.Extension.AIA.AccessDesc where

open Armor.Data.X509.Extension.AIA.AccessDesc.Parser public
open Armor.Data.X509.Extension.AIA.AccessDesc.TCB    public

module AccessDesc where
  open Armor.Data.X509.Extension.AIA.AccessDesc.Eq           public
  open Armor.Data.X509.Extension.AIA.AccessDesc.Properties   public
