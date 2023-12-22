open import Armor.Binary
open import Armor.Data.X509.GeneralNames
open import Armor.Data.X509.Extension.IAN.TCB
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.Extension.IAN.Parser where

open Armor.Grammar.Parallel UInt8
open Armor.Grammar.Parser   UInt8

private
  here' = "X509: Extension: IAN"

parseIANFields : Parser (Logging ∘ Dec) IANFields
parseIANFields =
  parseTLV _ here' _
    (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow")
      parseGeneralNames)
