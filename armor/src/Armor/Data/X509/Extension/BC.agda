import Armor.Data.X509.Extension.BC.Eq
import Armor.Data.X509.Extension.BC.Parser
import Armor.Data.X509.Extension.BC.Properties
import Armor.Data.X509.Extension.BC.TCB

module Armor.Data.X509.Extension.BC where

open Armor.Data.X509.Extension.BC.Parser public
open Armor.Data.X509.Extension.BC.TCB    public
  hiding (isCA)

module BC where
  open Armor.Data.X509.Extension.BC.Eq         public
  open Armor.Data.X509.Extension.BC.Properties public
  open Armor.Data.X509.Extension.BC.TCB        public
    using (isCA)
