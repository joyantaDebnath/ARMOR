open import Armor.Binary
open import Armor.Data.X509.Extension.BC.Properties
open import Armor.Data.X509.Extension.BC.TCB
open import Armor.Data.X690-DER.Boool
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.Sequence
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.Extension.BC.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

private
  here' = "X509: Extension: BC"

parseBCFieldsSeqFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength BCFieldsSeqFields n)
parseBCFieldsSeqFields n =
  parseEquivalent (Parallel.equivalent₁ equivalent)
    (Sequence.parseDefaultOption falseBoool here'
      Boool.unambiguous TLV.nosubstrings TLV.nosubstrings (TLV.noconfusion λ ())
        Boool.parse (Int.parse (here' String.++ ": CA")) _)

parseBCFieldsSeq : Parser (Logging ∘ Dec) BCFieldsSeq
parseBCFieldsSeq = parseTLV _ (here' String.++ ": Seq") _ parseBCFieldsSeqFields

parseBCFields : Parser (Logging ∘ Dec) BCFields
parseBCFields = parseTLV _ here' _ (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow") parseBCFieldsSeq)

-- private
--   module Test where

--     val₁ : List Dig
--     val₁ = # 4 ∷ # 2 ∷ # 48 ∷ [ # 0 ]

--     val₂ : List Dig
--     val₂ = # 4 ∷ # 5 ∷ # 48 ∷ # 3 ∷ # 1 ∷ # 1 ∷ [ # 255 ]

--     val₃ : List Dig
--     val₃ = # 4 ∷ # 8 ∷ # 48 ∷ # 6 ∷ # 1 ∷ # 1 ∷ # 255 ∷ # 2 ∷ # 1 ∷ [ # 0 ]

--     test₁ : X509.BCFields val₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseBCFields val₁)} tt)

--     test₂ : X509.BCFields val₂
--     test₂ = Success.value (toWitness {Q = Logging.val (runParser parseBCFields val₂)} tt)

--     test₃ : X509.BCFields val₃
--     test₃ = Success.value (toWitness {Q = Logging.val (runParser parseBCFields val₃)} tt)
