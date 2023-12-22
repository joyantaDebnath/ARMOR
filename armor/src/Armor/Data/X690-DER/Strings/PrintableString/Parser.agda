open import Armor.Binary
open import Armor.Data.X690-DER.Strings.PrintableString.Char
open import Armor.Data.X690-DER.Strings.PrintableString.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X690-DER.Strings.PrintableString.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.IList       UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

private
  here' = "X690-DER: Strings: PrintableString: "

  parseExact : ∀ n → Parser (Logging ∘ Dec) (ExactLength (IList PrintableStringChar) n)
  parseExact n =
    parseIList
      (tell $ here' String.++ "parseExact: underflow")
      _ Char.nonempty Char.nosubstrings Char.parse _

parsePrintableString : Parser (Logging ∘ Dec) PrintableString
parsePrintableString = parseTLV _ here' _ parseExact
