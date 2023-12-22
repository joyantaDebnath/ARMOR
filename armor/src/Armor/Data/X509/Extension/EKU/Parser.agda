open import Armor.Binary
open import Armor.Data.X509.Extension.EKU.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.Extension.EKU.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

private
  here' = "X509: Extension: EKU"

parseEKUFields : Parser (Logging ∘ Dec) EKUFields
parseEKUFields =
  parseTLV _ here' _
    (parseExactLength TLV.nosubstrings
      (tell $ here' String.++ ": underflow")
      (parseNonEmptySeq (here' String.++ ": elems") _ TLV.nonempty TLV.nosubstrings parseOID))

-- private
--   module Test where

--     val₁ : List Dig
--     val₁ = # 4 ∷ # 12 ∷ # 48 ∷ # 10 ∷ # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 3 ∷ [ # 1 ]

--     val₂ : List Dig
--     val₂ = # 4 ∷ # 22 ∷ # 48 ∷ # 20 ∷ # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 3 ∷ # 1 ∷ # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 3 ∷ [ # 2 ]

--     test₁ : X509.EKUFields val₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseEKUFields val₁)} tt)

--     test₂ : X509.EKUFields val₂
--     test₂ = Success.value (toWitness {Q = Logging.val (runParser parseEKUFields val₂)} tt)
