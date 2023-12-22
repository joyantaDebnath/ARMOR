import Armor.Data.X690-DER.Time.GeneralizedTime.Foreign
import Armor.Data.X690-DER.Time.GeneralizedTime.Ordering
import Armor.Data.X690-DER.Time.GeneralizedTime.Parser
import Armor.Data.X690-DER.Time.GeneralizedTime.Properties
import Armor.Data.X690-DER.Time.GeneralizedTime.TCB

module Armor.Data.X690-DER.Time.GeneralizedTime where

open Armor.Data.X690-DER.Time.GeneralizedTime.TCB public
  hiding (equivalent)

module GeneralizedTime where
  open Armor.Data.X690-DER.Time.GeneralizedTime.Foreign    public
  open Armor.Data.X690-DER.Time.GeneralizedTime.Ordering   public
    renaming ( compare-GeneralizedTimeFields< to <-compare
             ; _GeneralizedTimeFields≤?_ to _≤?_)
  open Armor.Data.X690-DER.Time.GeneralizedTime.Parser     public
  open Armor.Data.X690-DER.Time.GeneralizedTime.Properties public
  open Armor.Data.X690-DER.Time.GeneralizedTime.TCB        public
    using (equivalent)
