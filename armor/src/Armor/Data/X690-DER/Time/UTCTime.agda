import Armor.Data.X690-DER.Time.UTCTime.Parser
import Armor.Data.X690-DER.Time.UTCTime.Properties
import Armor.Data.X690-DER.Time.UTCTime.TCB

module Armor.Data.X690-DER.Time.UTCTime where

open Armor.Data.X690-DER.Time.UTCTime.TCB public
  hiding (equivalent)

module UTCTime where
  open Armor.Data.X690-DER.Time.UTCTime.Parser     public
  open Armor.Data.X690-DER.Time.UTCTime.Properties public
  open Armor.Data.X690-DER.Time.UTCTime.TCB        public
    using (equivalent)
