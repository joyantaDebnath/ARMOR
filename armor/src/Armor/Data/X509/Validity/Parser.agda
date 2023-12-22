open import Armor.Binary
open import Armor.Data.X509.Validity.TCB
open import Armor.Data.X509.Validity.Time
open import Armor.Data.X509.Validity.Properties
open import Armor.Data.X690-DER
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Validity.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Seq         UInt8

module parseValidityFields where
  here' = "X509: Validity"

  parseValidityFields : Parser (Logging ∘ Dec) ValidityFields
  parseValidityFields =
    parseEquivalent equivalent
      (parse& Time.nosubstrings Time.parse Time.parse)

open parseValidityFields public using (parseValidityFields)

parseValidity : Parser (Logging ∘ Dec) Validity
parseValidity =
  parseTLV _ parseValidityFields.here' _
    (parseExactLength nosubstrings
      (tell $ parseValidityFields.here' String.++ ": length mismatch")
      parseValidityFields)

-- private
--   module Test where

--     Validity₁ : List Dig
--     Validity₁ = Tag.Sequence ∷ # 32 ∷ # Tag.GeneralizedTime ∷ # 15 ∷ # 50 ∷ # 56 ∷ # 52 ∷ # 49 ∷ # 48 ∷ # 54 ∷ # 50 ∷ # 52 ∷ # 49 ∷ # 56 ∷ # 51 ∷ # 54 ∷ # 53 ∷ # 52 ∷ # 90 ∷ # Tag.UTCTime ∷ # 13 ∷ # 57 ∷ # 55 ∷ # 48 ∷ # 53 ∷ # 51 ∷ # 48 ∷ # 49 ∷ # 52 ∷ # 52 ∷ # 56 ∷ # 50 ∷ # 50 ∷ [ # 90 ]

--     test₁ : Validity Validity₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseValidity Validity₁)} tt)
