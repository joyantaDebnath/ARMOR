import Armor.Data.X509.Validity.Time.Ordering
import Armor.Data.X509.Validity.Time.Parser
import Armor.Data.X509.Validity.Time.Properties
import Armor.Data.X509.Validity.Time.TCB

module Armor.Data.X509.Validity.Time where

open Armor.Data.X509.Validity.Time.TCB public
  hiding (module Time ; equivalent ; getYear ; getMonth ; getDay ; getHour ; getMinute ; getSec)

module Time where
  open Armor.Data.X509.Validity.Time.Ordering   public
    renaming (_Time≤_ to _≤_ ; _Time≤?_ to _≤?_)
  open Armor.Data.X509.Validity.Time.Parser     public
  open Armor.Data.X509.Validity.Time.Properties public
  open Armor.Data.X509.Validity.Time.TCB        public
    using (equivalent ; getYear ; getMonth ; getDay ; getHour ; getMinute ; getSec)
