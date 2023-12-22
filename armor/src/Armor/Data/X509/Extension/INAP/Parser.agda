open import Armor.Binary
open import Armor.Data.X509.Extension.INAP.TCB
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.OctetString.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.Extension.INAP.Parser where

open Armor.Grammar.Parallel UInt8
open Armor.Grammar.Parser   UInt8

private
  here' = "X509: Extension: INAP"

parseINAPFields : Parser (Logging ∘ Dec) INAPFields
parseINAPFields =
  parseTLV _ here' _
    λ n → parseExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow") (Int.parse here') n

