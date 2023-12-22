import Armor.Data.X690-DER.Time.TimeType.Parser
import Armor.Data.X690-DER.Time.TimeType.Properties
import Armor.Data.X690-DER.Time.TimeType.Relation
import Armor.Data.X690-DER.Time.TimeType.TCB

module Armor.Data.X690-DER.Time.TimeType where

open Armor.Data.X690-DER.Time.TimeType.TCB public
  hiding (module TimeType ; encodeℕ)

module TimeType where
  open Armor.Data.X690-DER.Time.TimeType.Parser       public
  open Armor.Data.X690-DER.Time.TimeType.Properties   public
  open Armor.Data.X690-DER.Time.TimeType.Relation     public
    renaming
      ( _Time≤_ to _≤_
      ; _Time≥_ to _≥_
      ; _Time<_ to _<_
      ; _Time>_ to _>_
      ; _Time≡_ to _≡_)
  open Armor.Data.X690-DER.Time.TimeType.TCB public
    using (encodeℕ)
  open Armor.Data.X690-DER.Time.TimeType.TCB.TimeType public
