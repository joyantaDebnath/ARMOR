open import Armor.Binary
open import Armor.Data.X509.Extension.PC.TCB
open import Armor.Data.X509.Extension.PC.Properties
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.PC.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Seq         UInt8

private
  here' = "X509: Extension: PC"

parsePCFields : Parser (Logging ∘ Dec) PCFields
parsePCFields =
  parseTLV _ here' _
    (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow")
      (parseTLV _ here' _ helper))
  where
  helper : (n : ℕ) → Parser (Logging ∘ Dec) (ExactLength (PCFieldsSeqFields) n)
  helper n =
    parseEquivalent (Parallel.equivalent₁ equivalentPCFieldsSeqFields)
      (parseOption₂ here' TLV.nosubstrings TLV.nosubstrings (TLV.noconfusion λ ())
        (Int.[_]parse (here' String.++ " (require)" ) _)
        (Int.[_]parse (here' String.++ " (inhibit)") _) n)
