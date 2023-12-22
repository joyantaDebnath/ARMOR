open import Armor.Binary
open import Armor.Data.X509.PublicKey.Val.EC.TCB
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.OctetString
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq       
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Val.EC.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

private
  here' = "X509: PublicKey: Val: EC"

parseValue : ∀ n → Parser (Logging ∘ Dec) (ExactLength ECBitStringValue n)
parseValue n =
  parseEquivalent (Iso.symEquivalent Distribute.exactLength-&)
    (parse&ᵈ
      (Parallel.nosubstrings₁ λ where _ (─ refl) (─ refl) → refl)
      (Parallel.Length≤.unambiguous _ (erased-unique ≡-unique))
      (parse≤ n
        (parseLitE (tell $ here' String.++ ": underflow") (tell $ here' String.++ ": mismatch") [ # 0 ])
        (λ where _ (─ refl) (─ refl) → refl)
        (tell $ here' String.++ ": length overflow"))
        λ where
          (singleton r r≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength OctetStringValue (n ∸ x)))
              r≡ (OctetString.parseValue (n - r)))

parse : Parser (Logging ∘ Dec) ECBitString
parse = parseTLV _ here' _ parseValue
