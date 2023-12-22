open import Armor.Binary
open import Armor.Data.X690-DER.Time.Year.TCB
import      Armor.Data.X690-DER.Time.TimeType.Parser as TimeType
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X690-DER.Time.Year.Parser where

open Armor.Grammar.Parser UInt8

parse₂ : Parser (Logging ∘ Dec) Year₂
parse₂ = TimeType.parse _ _ _

parse₄ : Parser (Logging ∘ Dec) Year₄
parse₄ = TimeType.parse _ _ _
