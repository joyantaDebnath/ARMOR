open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.Basis
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.Properties
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.TCB
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

private
  here' = "X509: PublicKey: Alg: EC: ECPKParameters: ECParameters: FieldID: CharTwo"

parseFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength CharTwoFields n)
parseFields n =
  parseEquivalent equiv
     (parse&ᵈ
       (Parallel.nosubstrings₁ TLV.nosubstrings)
       (Parallel.Length≤.unambiguous _ Int.unambiguous)
       (parse≤ n (Int.parse here') TLV.nosubstrings (tell $ here' String.++ ": length overflow"))
       λ where
         {bs} (singleton r r≡) m →
           subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength BasisFields (n - x))) r≡
             (Basis.parse (n - r)))
  where
  equiv : Equivalent (&ₚᵈ (Length≤ _ _) (λ {bs₁} _ → ExactLength BasisFields (n - length bs₁))) (ExactLength CharTwoFields n)
  equiv = Iso.transEquivalent (Iso.symEquivalent Distribute.exactLength-&) (Parallel.equivalent₁{A₁ = CharTwoFieldsRep}{A₂ = CharTwoFields} equivalent)

parse : Parser (Logging ∘ Dec) CharTwo
parse = parseTLV _ here' _ parseFields
