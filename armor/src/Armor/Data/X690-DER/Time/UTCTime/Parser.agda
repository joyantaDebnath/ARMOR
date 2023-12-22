open import Armor.Binary
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.Time.UTCTime.Properties
open import Armor.Data.X690-DER.Time.UTCTime.TCB
open import Armor.Data.X690-DER.Time.MDHMS
open import Armor.Data.X690-DER.Time.TimeType
open import Armor.Data.X690-DER.Time.Year
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X690-DER.Time.UTCTime.Parser where

open Armor.Grammar.Parallel UInt8
open Armor.Grammar.Parser   UInt8
open Armor.Grammar.Seq      UInt8

private
  here' = "X690-DER: Generalized Time"

parseFields : Parser (Logging ∘ Dec) UTCTimeFields
parseFields = parseEquivalent equivalent p
  where
  p : Parser (Logging ∘ Dec) UTCTimeFieldsRep
  p =  parse& TimeType.nosubstrings Year.parse₂
      (parse& MDHMS.nosubstrings MDHMS.parse
      (parseLitE
        (tell $ here' String.++ ": underflow")
        (tell $ here' String.++ ": mismatch (Z)")
        [ # 'Z' ]))

parse : Parser (Logging ∘ Dec) UTCTime
parse = parseTLV _ here' _
          (parseExactLength nosubstrings
            (tell $ here' String.++ " (fields): length mismatch")
            parseFields)
