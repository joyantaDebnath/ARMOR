open import Armor.Binary
open import Armor.Data.X509.Extension.AIA.AccessDesc
open import Armor.Data.X509.Extension.AIA.TCB
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.Extension.AIA.Parser where

open Armor.Grammar.Parser   UInt8
open Armor.Grammar.Parallel UInt8

private
  here' = "X509: Extension: AIA"

parseAIAFields : Parser (Logging ∘ Dec) AIAFields
parseAIAFields =
  parseTLV _ here' _ (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow")
    (parseNonEmptySeq (here' String.++ ": elems") _ TLV.nonempty TLV.nosubstrings parseAccessDesc))
