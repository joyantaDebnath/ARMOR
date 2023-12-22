open import Armor.Binary
open import Armor.Data.X509.SignAlg.RSA.TCB
import      Armor.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.Sequence.DefinedByOID
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.Null
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Grammar.Option
open import Armor.Data.X690-DER.OctetString
open import Armor.Prelude

module Armor.Data.X509.SignAlg.RSA.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

private
  here' = "X509: SignAlg: RSA"

parseParams : ∀ n {@0 bs} → (o : OID bs) (o∈? : Dec ((-, TLV.val o) ∈ OIDs.RSA.Supported))
              → Parser (Logging ∘ Dec) (ExactLength (RSAParams' o o∈?) n)
parseParams n o (no ¬p) =
  parseExactLength (λ where _ ()) silent parseFalse n
parseParams n o (yes p) =
  case splitRSA∈ o p
    ret (λ ∈? → Parser (Logging ∘ Dec) (ExactLength (RSAParams“ o ∈?) n))
    of λ where
    (inj₁ x) → parseExactLength TLV.nosubstrings
                 (tell $ here' String.++ ": parameter should be null") Null.parse n
    (inj₂ (inj₁ x)) → Option.parseOption₁ExactLength _ TLV.nosubstrings
                  (tell $ here' String.++ ": parameter should be null or absent") Null.parse n
    (inj₂ (inj₂ y)) → parseExactLength TLV.nosubstrings
                         (tell $ here' String.++ ": parameter must be present")
                         (parseTLV _ "TLV underflow" _ OctetString.parseValue)
                         n
 
parse : Parser (Logging ∘ Dec) RSA
parse = DefinedByOID.parse here' λ n o → parseParams n o (((-, TLV.val o) ∈? OIDs.RSA.Supported))
