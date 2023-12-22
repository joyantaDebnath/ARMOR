open import Armor.Binary
open import Armor.Data.X690-DER.Time.Month.TCB
import      Armor.Data.X690-DER.Time.TimeType.Parser as TimeType
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X690-DER.Time.Month.Parser where

open Armor.Grammar.Parser UInt8

parse : Parser (Logging ∘ Dec) Month
parse = TimeType.parse _ _ _
