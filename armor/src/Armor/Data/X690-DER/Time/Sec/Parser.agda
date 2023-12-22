open import Armor.Binary
open import Armor.Data.X690-DER.Time.Sec.TCB
import      Armor.Data.X690-DER.Time.TimeType.Parser as TimeType
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X690-DER.Time.Sec.Parser where

open Armor.Grammar.Parser UInt8

parse : Parser (Logging ∘ Dec) Sec
parse = TimeType.parse _ _ _
