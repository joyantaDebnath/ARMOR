open import Armor.Binary
open import Armor.Data.X509.Extension.SKI.TCB
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.Extension.SKI.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

private
  here' = "X509: Extension: SKI"

parseSKIFields : Parser (Logging ∘ Dec) SKIFields
parseSKIFields =
  parseTLV _ "SKI Fields" _
    (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow") OctetString.parse)

-- private
--   module Test where

--     val₁ : List Dig
--     val₁ = # 4 ∷ # 22 ∷ # 4 ∷ # 20 ∷ # 147 ∷ # 61 ∷ # 128 ∷ # 160 ∷ # 120 ∷ # 95 ∷ # 164 ∷ # 18 ∷ # 101 ∷ # 194 ∷ # 57 ∷ # 173 ∷ # 54 ∷ # 77 ∷ # 116 ∷ # 177 ∷ # 171 ∷ # 84 ∷ # 108 ∷ [ # 167 ]

--     test₁ : X509.SKIFields val₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseSKIFields val₁)} tt)
