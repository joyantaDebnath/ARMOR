import Armor.Data.X690-DER.Sequence.DefinedByOID.Parser
import Armor.Data.X690-DER.Sequence.DefinedByOID.Properties
import Armor.Data.X690-DER.Sequence.DefinedByOID.TCB

module Armor.Data.X690-DER.Sequence.DefinedByOID where

open Armor.Data.X690-DER.Sequence.DefinedByOID.TCB    public
  hiding (equivalent)

module DefinedByOID where
  open Armor.Data.X690-DER.Sequence.DefinedByOID.Parser     public
  open Armor.Data.X690-DER.Sequence.DefinedByOID.Properties public
  open Armor.Data.X690-DER.Sequence.DefinedByOID.TCB    public
    using (equivalent)
