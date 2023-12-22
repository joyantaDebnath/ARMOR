open import Armor.Binary
open import Armor.Data.Unicode.UTF8
open import Armor.Data.X690-DER.Strings.UTF8String.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X690-DER.Strings.UTF8String.Parser where

open Armor.Grammar.Parser UInt8

private
  here' = "X690-DER: Strings: UTF8String: parse"

parseUTF8String : Parser (Logging ∘ Dec) UTF8String
parseUTF8String =
  parseTLV Tag.UTF8String here' _ parseUTF8
