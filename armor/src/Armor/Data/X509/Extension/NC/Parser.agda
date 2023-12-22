open import Armor.Binary
open import Armor.Data.X509.Extension.NC.GeneralSubtree
open import Armor.Data.X509.Extension.NC.Properties
open import Armor.Data.X509.Extension.NC.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.SequenceOf
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.NC.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Seq         UInt8
open Armor.Grammar.IList       UInt8

private
  here' = "X509: Extension: NC"

parseNCFields : Parser (Logging ∘ Dec) NCFields
parseNCFields =
  parseTLV _ here' _
    (parseExactLength TLV.nosubstrings
      (tell $ here' String.++ ": underflow")
      (parseTLV _ here' _ helper))
  where
  helper : (n : ℕ) → Parser (Logging ∘ Dec) (ExactLength (NCFieldsSeqFields) n)
  helper n =  parseEquivalent
      (Parallel.equivalent₁ equivalentNCFieldsSeqFields)
      (parseOption₂ here' TLV.nosubstrings TLV.nosubstrings (TLV.noconfusion λ ())
        (parseTLV _ (here' String.++ " (permit)") _ parseExactLengthGeneralSubtrees)
        (parseTLV _ (here' String.++ " (exclude)") _ parseExactLengthGeneralSubtrees)
        n)
