open import Armor.Prelude

open import Armor.Binary
open import Armor.Data.X509.Extension.KU.TCB
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser

module Armor.Data.X509.Extension.KU.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

private
  here' = "X509: Extension: KU"

parseKUFields : Parser (Logging ∘ Dec) KUFields
parseKUFields =
  parseTLV _ here' _
    (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow")
      parseBitstring)

-- private
--   module Test where

--     val₁ : List UInt8
--     val₁ = # 4 ∷ # 6 ∷ # 3 ∷ # 4 ∷ # 6 ∷ # 160 ∷ # 0 ∷ [ # 0 ]

--     val₂ : List UInt8
--     val₂ = # 4 ∷ # 4 ∷ # 3 ∷ # 2 ∷ # 4 ∷ [ # 160 ]

--     val₃ : List UInt8
--     val₃ = # 4 ∷ # 4 ∷ # 3 ∷ # 2 ∷ # 6 ∷ [ # 160 ]

--     test₁ : KUFields val₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseKUFields val₁)} tt)

--     test₂ : KUFields val₂
--     test₂ = Success.value (toWitness {Q = Logging.val (runParser parseKUFields val₂)} tt)

    -- test₃ : ¬ Success _ KUFields val₃
    -- test₃ = toWitnessFalse {Q = Logging.val (runParser parseKUFields val₃)}
