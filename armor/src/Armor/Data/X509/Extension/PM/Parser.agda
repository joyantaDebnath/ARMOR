open import Armor.Binary
open import Armor.Data.X509.Extension.PM.Properties
open import Armor.Data.X509.Extension.PM.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.SequenceOf
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.PM.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Seq         UInt8

private
  here' = "X509: Extension: PM"

parsePolicyMapFields : Parser (Logging ∘ Dec) PolicyMapFields
parsePolicyMapFields =
  parseEquivalent equivalentPolicyMapFields
    (parse& TLV.nosubstrings parseOID parseOID)

parsePMFields : Parser (Logging ∘ Dec) PMFields
parsePMFields =
  parseTLV _ here' _
    (parseExactLength  TLV.nosubstrings (tell $ here' String.++ ": underflow")
      (parseNonEmptySeq here' _ TLV.nonempty TLV.nosubstrings
        (parseTLV _ here' _
          (λ n → parseExactLength nosubstrings (tell $ here' String.++ ": underflow") parsePolicyMapFields n))))
