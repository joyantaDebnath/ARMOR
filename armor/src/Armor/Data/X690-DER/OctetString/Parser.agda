open import Armor.Binary
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.OctetString.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X690-DER.OctetString.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

private
  here' = "X690-DER: OctetString"

parseValue : ∀ n → Parser (Logging ∘ Dec) (ExactLength OctetStringValue n)
parseValue = λ n → parseN n (tell $ here' String.++ " (value): underflow")

parse : Parser (Logging ∘ Dec) OctetString
parse = parseTLV Tag.OctetString here' OctetStringValue parseValue
