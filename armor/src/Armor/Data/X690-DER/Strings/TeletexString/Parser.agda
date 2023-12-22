open import Armor.Binary
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.Strings.TeletexString.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X690-DER.Strings.TeletexString.Parser where

open Armor.Grammar.Parser UInt8

private
  here' = "X690-DER: Strings: TeletexString: parse"

parseTeletexString : Parser (Logging ∘ Dec) TeletexString
parseTeletexString =
  parseTLV Tag.TeletexString here' _ OctetString.parseValue
