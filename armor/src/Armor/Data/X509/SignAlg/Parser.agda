open import Armor.Prelude

open import Armor.Binary
open import Armor.Data.X509.SignAlg.DSA
open import Armor.Data.X509.SignAlg.ECDSA
open import Armor.Data.X509.SignAlg.Properties
open import Armor.Data.X509.SignAlg.RSA
open import Armor.Data.X509.SignAlg.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.Sequence.DefinedByOID
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Properties
import      Armor.Grammar.Sum

module Armor.Data.X509.SignAlg.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Sum         UInt8

private
  here' = "X509: SignAlg"

parseParam : ∀ n {@0 bs} (o : OID bs) → Parser (Logging ∘ Dec) (ExactLength (SignAlgParam o) n)
parseParam n o =
  case isSupported o
  ret (λ o∈? → Parser (Logging ∘ Dec) (ExactLength (SignAlgParam' o o∈?) n))
  of λ where
    (no ¬p) → parseN _ (tell $ here' String.++ " (param): underflow")
    (yes o∈) →
      case lookupSignAlg o o∈
      ret (λ o∈ → Parser (Logging ∘ Dec) (ExactLength (SignAlgParam“ o o∈) n))
      of λ where
        (inj₁ x) →
          parseExactLength
            (λ where _ (─ refl) (─ refl) → refl)
            silent
            (parseErased (parseLit silent silent []))
            _
        (inj₂ (inj₁ x)) →
          parseExactLength
            (λ where _ (─ refl) (─ refl) → refl)
            silent
            (parseErased (parseLit silent silent []))
            _
        (inj₂ (inj₂ y)) →
          RSA.parseParams n o (yes y)

parse : Parser (Logging ∘ Dec) SignAlg
parse =
  DefinedByOID.parse here' parseParam
