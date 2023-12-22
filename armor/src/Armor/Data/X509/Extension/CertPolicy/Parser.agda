open import Armor.Binary
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation
open import Armor.Data.X509.Extension.CertPolicy.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.Extension.CertPolicy.Parser where

open Armor.Grammar.Parallel UInt8
open Armor.Grammar.Parser   UInt8

private
  here' = "X509: Extension: CertPolicy"

parseCertPolFieldsSeq : Parser (Logging ∘ Dec) CertPolFieldsSeq
parseCertPolFieldsSeq = parseNonEmptySeq (here' String.++ " (fields)") _ TLV.nonempty TLV.nosubstrings parsePolicyInformation

parseCertPolFields : Parser (Logging ∘ Dec) CertPolFields
parseCertPolFields =
  parseTLV _ here' _
    (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": overflow") parseCertPolFieldsSeq)
