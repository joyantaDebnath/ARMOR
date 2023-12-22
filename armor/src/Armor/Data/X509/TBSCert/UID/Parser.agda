open import Armor.Binary
open import Armor.Data.X509.TBSCert.UID.TCB
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.TBSCert.UID.Parser where

open Armor.Grammar.Parser UInt8

private
  here' = "X509: TBSCert: UID"

parseIssUID : Parser (Logging ∘ Dec) IssUID
parseIssUID =
  parseTLV Tag.A81 (here' String.++ ": issuer") BitStringValue parseBitstringValue

parseSubUID : Parser (Logging ∘ Dec) SubUID
parseSubUID =
  parseTLV Tag.A82 (here' String.++ ": subject") BitStringValue parseBitstringValue
