open import Armor.Binary
open import Armor.Data.X509.Extension.AKI.Properties
import      Armor.Data.X509.Extension.AKI.TCB as AKI
open import Armor.Data.X509.GeneralNames
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Seq
open import Armor.Prelude
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Armor.Data.X509.Extension.AKI.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Seq         UInt8

module parseAKIFields where
  module Here where
    AKIKeyId = "X509: Extension: AKI: key id"
    AKIAuthCertIssuer = "X509: Extension: AKI: authority key issuer"
    AKIAuthCertSN = "X509: Extension: AKI: authority certificate serial number"
    AKI = "X509: Extension: AKI"

  open AKI
  open ≡-Reasoning

  parseAKIKeyId : Parser (Logging ∘ Dec) AKIKeyId
  parseAKIKeyId = parseTLV _ Here.AKIKeyId _ OctetString.parseValue

  parseAKIAuthCertIssuer : Parser (Logging ∘ Dec) AKIAuthCertIssuer
  parseAKIAuthCertIssuer = parseTLV _ Here.AKIAuthCertIssuer _ parseGeneralNamesElems

  parseAKIAuthCertSN : Parser (Logging ∘ Dec) AKIAuthCertSN
  parseAKIAuthCertSN = parseTLV _ Here.AKIAuthCertSN _ (Int.parseValue Here.AKIAuthCertSN)

  -- NOTE: The proof effort caught a bug in my original implementation :)
  -- (Try to parse all, then check lengths)
  parseAKIFieldsSeqFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength AKIFieldsSeqFields n)
  parseAKIFieldsSeqFields n =
    parseEquivalent (Parallel.equivalent₁ equivalentAKIFieldsSeqFields)
      (parse₂Option₃ "X509: Extension: AKI (fields)"
        TLV.nosubstrings TLV.nosubstrings TLV.nosubstrings
        (TLV.noconfusion λ ()) (TLV.noconfusion λ ()) (TLV.noconfusion λ ())
        parseAKIKeyId parseAKIAuthCertIssuer parseAKIAuthCertSN
        n)

  parseAKIFieldsSeq : Parser (Logging ∘ Dec) AKIFieldsSeq
  parseAKIFieldsSeq =
    parseTLV _ Here.AKI _ parseAKIFieldsSeqFields

  parseAKIFields : Parser (Logging ∘ Dec) AKIFields
  parseAKIFields =
    parseTLV _ Here.AKI _ (parseExactLength TLV.nosubstrings
      (tell $ Here.AKI String.++ ": overflow") parseAKIFieldsSeq)

open parseAKIFields public using
  (parseAKIKeyId ; parseAKIAuthCertIssuer ; parseAKIAuthCertSN ; parseAKIFieldsSeqFields ; parseAKIFields)


-- private
--   module Test where

--     val₁ : List UInt8
--     val₁ = # 128 ∷ # 20 ∷ # 111 ∷ # 213 ∷ # 99 ∷ # 241 ∷ # 222 ∷ # 168 ∷ # 109 ∷ # 19 ∷ # 190 ∷ # 148 ∷ # 167 ∷ # 149 ∷ # 7 ∷ # 124 ∷ # 28 ∷ # 72 ∷ # 193 ∷ # 23 ∷ # 66 ∷ [ # 97 ]

--     val₂ : List UInt8
--     val₂ = # 161 ∷ # 115 ∷ # 164 ∷ # 113 ∷ # 48 ∷ # 111 ∷ # 49 ∷ # 11 ∷ # 48 ∷ # 9 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ # 83 ∷ # 49 ∷ # 11 ∷ # 48 ∷ # 9 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 8 ∷ # 19 ∷ # 2 ∷ # 67 ∷ # 65 ∷ # 49 ∷ # 17 ∷ # 48 ∷ # 15 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 7 ∷ # 19 ∷ # 8 ∷ # 83 ∷ # 97 ∷ # 110 ∷ # 32 ∷ # 74 ∷ # 111 ∷ # 115 ∷ # 101 ∷ # 49 ∷ # 29 ∷ # 48 ∷ # 27 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 10 ∷ # 19 ∷ # 20 ∷ # 67 ∷ # 97 ∷ # 109 ∷ # 98 ∷ # 105 ∷ # 117 ∷ # 109 ∷ # 32 ∷ # 78 ∷ # 101 ∷ # 116 ∷ # 119 ∷ # 111 ∷ # 114 ∷ # 107 ∷ # 115 ∷ # 32 ∷ # 73 ∷ # 110 ∷ # 99 ∷ # 49 ∷ # 17 ∷ # 48 ∷ # 15 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 11 ∷ # 19 ∷ # 8 ∷ # 80 ∷ # 114 ∷ # 111 ∷ # 100 ∷ # 117 ∷ # 99 ∷ # 116 ∷ # 115 ∷ # 49 ∷ # 14 ∷ # 48 ∷ # 12 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 3 ∷ # 19 ∷ # 5 ∷ # 82 ∷ # 49 ∷ # 57 ∷ # 48 ∷ [ # 87 ]

--     val₃ : List UInt8
--     val₃ = # 130 ∷ # 9 ∷ # 0 ∷ # 148 ∷ # 56 ∷ # 18 ∷ # 160 ∷ # 125 ∷ # 219 ∷ # 197 ∷ [ # 226 ]

--     val₄ : List UInt8
--     val₄ = # 4 ∷ # 129 ∷ # 153 ∷ # 48 ∷ # 129 ∷ # 150 ∷ # 128 ∷ # 20 ∷ # 111 ∷ # 213 ∷ # 99 ∷ # 241 ∷ # 222 ∷ # 168 ∷ # 109 ∷ # 19 ∷ # 190 ∷ # 148 ∷ # 167 ∷ # 149 ∷ # 7 ∷ # 124 ∷ # 28 ∷ # 72 ∷ # 193 ∷ # 23 ∷ # 66 ∷ # 97 ∷ # 161 ∷ # 115 ∷ # 164 ∷ # 113 ∷ # 48 ∷ # 111 ∷ # 49 ∷ # 11 ∷ # 48 ∷ # 9 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ # 83 ∷ # 49 ∷ # 11 ∷ # 48 ∷ # 9 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 8 ∷ # 19 ∷ # 2 ∷ # 67 ∷ # 65 ∷ # 49 ∷ # 17 ∷ # 48 ∷ # 15 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 7 ∷ # 19 ∷ # 8 ∷ # 83 ∷ # 97 ∷ # 110 ∷ # 32 ∷ # 74 ∷ # 111 ∷ # 115 ∷ # 101 ∷ # 49 ∷ # 29 ∷ # 48 ∷ # 27 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 10 ∷ # 19 ∷ # 20 ∷ # 67 ∷ # 97 ∷ # 109 ∷ # 98 ∷ # 105 ∷ # 117 ∷ # 109 ∷ # 32 ∷ # 78 ∷ # 101 ∷ # 116 ∷ # 119 ∷ # 111 ∷ # 114 ∷ # 107 ∷ # 115 ∷ # 32 ∷ # 73 ∷ # 110 ∷ # 99 ∷ # 49 ∷ # 17 ∷ # 48 ∷ # 15 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 11 ∷ # 19 ∷ # 8 ∷ # 80 ∷ # 114 ∷ # 111 ∷ # 100 ∷ # 117 ∷ # 99 ∷ # 116 ∷ # 115 ∷ # 49 ∷ # 14 ∷ # 48 ∷ # 12 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 3 ∷ # 19 ∷ # 5 ∷ # 82 ∷ # 49 ∷ # 57 ∷ # 48 ∷ # 87 ∷ # 130 ∷ # 9 ∷ # 0 ∷ # 148 ∷ # 56 ∷ # 18 ∷ # 160 ∷ # 125 ∷ # 219 ∷ # 197 ∷ [ # 226 ]

--     test₁ : AKI.AKIKeyId val₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseAKIKeyId val₁)} tt)

--     test₂ : AKI.AKIAuthCertIssuer val₂
--     test₂ = Success.value (toWitness {Q = Logging.val (runParser parseAKIAuthCertIssuer val₂)} tt)

--     test₃ : AKI.AKIAuthCertSN val₃
--     test₃ = Success.value (toWitness {Q = Logging.val (runParser parseAKIAuthCertSN val₃)} tt)

--     test₄ : AKI.AKIFields val₄
--     test₄ = Success.value (toWitness {Q = Logging.val (runParser parseAKIFields val₄)} tt)
