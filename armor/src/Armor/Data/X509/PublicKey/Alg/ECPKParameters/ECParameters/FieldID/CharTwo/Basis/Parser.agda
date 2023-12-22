open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.Basis.Properties
import      Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.Basis.TCB.OIDs as OIDs
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.Basis.TCB
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.Null
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.Sequence.DefinedByOID
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.Basis.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Seq         UInt8

private
  here' = "X509: PublicKey: Alg: ECPKParameters: ECParameters: FieldID: CharTwo: Basis"

parseParameters : ∀ n {@0 bs} (o : OID bs) → Parser (Logging ∘ Dec) (ExactLength (BasisParameters o) n)
parseParameters n o =
  case (-, TLV.val o) ∈? OIDs.Supported
  ret (λ o∈? → Parser (Logging ∘ Dec) (ExactLength (BasisParameters' o o∈?) n))
  of λ where
    (no ¬p) → mkParser $ λ xs → do
      tell $ here' String.++ ": unsupported OID: " String.++ show (map (map toℕ) (Raw.to RawOID o))
      return ∘ no $ λ ()
    (yes (here px)) →
      parseExactLength TLV.nosubstrings (tell $ here' String.++ ": GNBasis: could not parse null parameter") Null.parse _
    (yes (there (here px))) →
      parseExactLength TLV.nosubstrings (tell $ here' String.++ ": TPBasis: could not parse parameter") (Int.parse here') _
    (yes (there (there (here px)))) →
      parseExactLength (Seq.nosubstrings TLV.nosubstrings (Seq.nosubstrings TLV.nosubstrings TLV.nosubstrings))
        (tell $ here' String.++ ": PPBasis: could not parse parameter")
        (parse& TLV.nosubstrings (Int.parse here') (parse& TLV.nosubstrings (Int.parse here') (Int.parse here')))
       _

parse : ∀ n → Parser (Logging ∘ Dec) (ExactLength BasisFields n)
parse = DefinedByOID.parseFields here' parseParameters
