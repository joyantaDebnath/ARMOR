import Armor.Data.X690-DER.Time.MDHMS.Ordering
import Armor.Data.X690-DER.Time.MDHMS.Parser
import Armor.Data.X690-DER.Time.MDHMS.Properties
import Armor.Data.X690-DER.Time.MDHMS.TCB

module Armor.Data.X690-DER.Time.MDHMS where

open Armor.Data.X690-DER.Time.MDHMS.TCB public
  hiding (module MDHMS ; equivalent ; _MDHMS<'_ ; _MDHMS<_ ; _MDHMS≤_)

module MDHMS where
  open Armor.Data.X690-DER.Time.MDHMS.Ordering   public
    renaming (trans-MDHMS<' to trans<' ; compare-MDHMS< to compare ; _MDHMS≤?_ to _≤?_)
  open Armor.Data.X690-DER.Time.MDHMS.Parser     public
  open Armor.Data.X690-DER.Time.MDHMS.Properties public
  open Armor.Data.X690-DER.Time.MDHMS.TCB        public
    using (equivalent)
    renaming (_MDHMS<'_ to _<'_ ; _MDHMS<_ to _<_ ; _MDHMS≤_ to _≤_)
  open Armor.Data.X690-DER.Time.MDHMS.TCB.MDHMS  public
