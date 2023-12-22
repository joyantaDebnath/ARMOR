import Armor.Data.X690-DER.Default.Parser
import Armor.Data.X690-DER.Default.Properties
import Armor.Data.X690-DER.Default.TCB

module Armor.Data.X690-DER.Default where

open Armor.Data.X690-DER.Default.TCB public
  using (Default ; RawDefault ; mkDefault)
  hiding (module Default)

module Default where
  open Armor.Data.X690-DER.Default.Parser     public
  open Armor.Data.X690-DER.Default.Properties public
  open Armor.Data.X690-DER.Default.TCB        public
    hiding (Default ; RawDefault)
  open Armor.Data.X690-DER.Default.TCB.Default public
