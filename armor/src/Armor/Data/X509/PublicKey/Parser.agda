open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg
open import Armor.Data.X509.PublicKey.Properties
open import Armor.Data.X509.PublicKey.TCB
open import Armor.Data.X509.PublicKey.Val
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

private
  here' = "X509: PublicKey"

parseFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength PublicKeyFields n)
parseFields n =
  parseEquivalent eq p₁
  where
  A = Length≤ PublicKeyAlg n
  B : {@0 bs : List UInt8} → (a : A bs) → @0 List UInt8 → Set
  B{bs} a = ExactLength (PublicKeyVal (fstₚ a)) (n - length bs)

  eq : Equivalent (&ₚᵈ A B) (ExactLength PublicKeyFields n)
  eq = Iso.transEquivalent (Iso.symEquivalent (Distribute.exactLength-&ᵈ)) (Parallel.equivalent₁ equivalent)

  p₁ : Parser (Logging ∘ Dec) (&ₚᵈ A B)
  p₁ =
    parse&ᵈ
      (Parallel.nosubstrings₁ TLV.nosubstrings)
      (Parallel.Length≤.unambiguous PublicKeyAlg Alg.unambiguous)
      (parse≤ n Alg.parse TLV.nosubstrings
        (tell $ here' String.++ " (alg): overflow"))
      λ where
        (singleton r r≡) a →
          subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength (PublicKeyVal (fstₚ a)) (n - x)))
            r≡
            (parseExactLength
              (Val.nosubstrings (fstₚ a))
              (tell $ here' String.++ " (val): length mismatch")
              (Val.parse (fstₚ a)) (n - r))

parse : Parser (Logging ∘ Dec) PublicKey
parse = parseTLV _ here' _ parseFields
