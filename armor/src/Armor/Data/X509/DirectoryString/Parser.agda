open import Armor.Prelude

open import Armor.Binary
open import Armor.Data.X509.DirectoryString.Properties
open import Armor.Data.X509.DirectoryString.TCB
open import Armor.Data.X690-DER
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Armor.Data.X509.DirectoryString.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parser UInt8

module parseDirectoryString where
  here' = "parseDirectoryString"
  open ≡-Reasoning

  parseDirectoryString : Parser (Logging ∘ Dec) DirectoryString
  runParser parseDirectoryString xs = do
    no ¬teletex ← runParser (parseTLVNonEmpty parseTeletexString) xs
      where yes t → return (yes (mapSuccess (λ {bs} → teletexString{bs}) t))
    no ¬printable ← runParser (parseTLVNonEmpty parsePrintableString) xs
      where yes p → return (yes (mapSuccess (λ {bs} → printableString{bs}) p))
    no ¬universal ← runParser (parseTLVNonEmpty parseUniversalString) xs
      where yes u → return (yes (mapSuccess (λ {bs} → universalString{bs}) u))
    no ¬utf8 ← runParser (parseTLVNonEmpty parseUTF8String) xs
      where yes u → return (yes (mapSuccess (λ {bs} → utf8String{bs}) u))
    no ¬bmp ← runParser (parseTLVNonEmpty parseBMPString) xs
      where yes b → return (yes (mapSuccess (λ {bs} → bmpString{bs}) b))
    return ∘ no $ λ where
      (success prefix read read≡ (teletexString x) suffix ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬teletex
      (success prefix read read≡ (printableString x) suffix ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬printable
      (success prefix read read≡ (universalString x) suffix ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬universal
      (success prefix read read≡ (utf8String x) suffix ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬utf8
      (success prefix read read≡ (bmpString x) suffix ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬bmp

open parseDirectoryString public using (parseDirectoryString)

-- private                         
--   module Test where

--   Dir₁ : List Dig
--   Dir₁ = Tag.TeletexString ∷ # 2 ∷ # 85 ∷ [ # 87 ]

--   Dir₂ : List Dig
--   Dir₂ = Tag.PrintableString ∷ # 2 ∷ # 85 ∷ [ # 87 ]


--   test₁ : DirectoryString Dir₁
--   test₁ = Success.value (toWitness {Q = Logging.val (runParser parseDirectoryString Dir₁)} tt)

--   test₂ : DirectoryString Dir₂
--   test₂ = Success.value (toWitness {Q = Logging.val (runParser parseDirectoryString Dir₂)} tt)
