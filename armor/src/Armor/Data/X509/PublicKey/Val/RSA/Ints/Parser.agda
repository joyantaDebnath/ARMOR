open import Armor.Binary
open import Armor.Data.X509.PublicKey.Val.RSA.Ints.Properties
open import Armor.Data.X509.PublicKey.Val.RSA.Ints.TCB
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Val.RSA.Ints.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Seq         UInt8

private
  here' = "X509: PublicKey: Val: RSA: Ints:"

parseFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength RSAPkIntsFields n)
parseFields =
  parseExactLength nosubstrings (tell $ here' String.++ ": underflow")
    (parseEquivalent equivalent (parse& TLV.nosubstrings (Int.parse here') (Int.parse here')))

parse :  Parser (Logging ∘ Dec) RSAPkInts
parse = parseTLV _ here' _ parseFields
