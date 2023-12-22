open import Armor.Binary
open import Armor.Data.X509.PublicKey.Val.RSA.Ints
open import Armor.Data.X509.PublicKey.Val.RSA.Properties
open import Armor.Data.X509.PublicKey.Val.RSA.TCB
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Val.RSA.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Seq         UInt8

private
  here' = "X509: PublicKey: Val: RSA" 

parseFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength RSABitStringFields n)
parseFields n =
  parseExactLength nosubstrings (tell $ here' String.++ ": underflow")
    (parseEquivalent equivalent
      (parse& (λ where _ (─ refl) (─ refl) → refl)
        (parseLitE
          (tell $ here' String.++ ": zero bit: underflow")
          (tell $ here' String.++ ": zero bit: mismatch")
          [ # 0 ])
        Ints.parse))
    n

parse :  Parser (Logging ∘ Dec) RSABitString
parse = parseTLV _ here' _ parseFields
