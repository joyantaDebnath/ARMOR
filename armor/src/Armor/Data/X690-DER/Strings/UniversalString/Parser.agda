open import Armor.Binary
open import Armor.Data.X690-DER.Strings.UniversalString.TCB
open import Armor.Data.X690-DER.TLV
open import Armor.Data.Unicode.UTF32
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X690-DER.Strings.UniversalString.Parser where

open Armor.Grammar.Parser UInt8

parseUniversalString : Parser (Logging ∘ Dec) UniversalString
parseUniversalString =
  parseTLV _ "X690-DER: Strings: UniversalString: parse:" _ UTF32.parse
