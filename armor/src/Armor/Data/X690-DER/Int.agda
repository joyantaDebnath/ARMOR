import Armor.Data.X690-DER.Int.Parser
import Armor.Data.X690-DER.Int.Properties
-- import Armor.Data.X690-DER.Int.Serializer
import Armor.Data.X690-DER.Int.TCB

module Armor.Data.X690-DER.Int where

open Armor.Data.X690-DER.Int.TCB public
  hiding (getVal)

module Int where
  open Armor.Data.X690-DER.Int.Parser public
  open Armor.Data.X690-DER.Int.Properties public
  open Armor.Data.X690-DER.Int.TCB public
    using (getVal)
