open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg
import      Armor.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
open import Armor.Data.X509.PublicKey.Val.EC
open import Armor.Data.X509.PublicKey.Val.RSA
open import Armor.Data.X509.PublicKey.Val.TCB
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Val.Parser where

open Armor.Grammar.Parser UInt8

parse : ∀ {@0 bs} → (a : PublicKeyAlg bs) → Parser (Logging ∘ Dec) (PublicKeyVal a)
parse a =
  case (-, TLV.val (Alg.getOID a)) ∈? OIDs.Supported
  ret (λ o∈? → Parser (Logging ∘ Dec) (PublicKeyVal' a o∈?))
  of λ where
    (no ¬p) → parseBitstring
    (yes (here px)) → RSA.parse
    (yes (there (here px))) → EC.parse
