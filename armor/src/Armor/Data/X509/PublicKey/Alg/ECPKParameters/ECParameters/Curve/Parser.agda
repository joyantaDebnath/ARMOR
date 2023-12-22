open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.Properties
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.TCB
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

private
  here' = "X509: PublicKey: Alg: EC: ECPKParameters: ECParameters: Curve"

parseFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength CurveFields n)
parseFields n =
  parseEquivalent
    (Iso.transEquivalent (Iso.symEquivalent Distribute.exactLength-&) (Parallel.equivalent₁ equivalent))
    (parse&ᵈ (Parallel.nosubstrings₁ (Seq.nosubstrings TLV.nosubstrings  TLV.nosubstrings))
      (Parallel.Length≤.unambiguous _
        (Seq.unambiguous OctetString.unambiguous
          TLV.nosubstrings OctetString.unambiguous))
      (parse≤ n (parse& TLV.nosubstrings  OctetString.parse OctetString.parse)
        (Seq.nosubstrings TLV.nosubstrings TLV.nosubstrings) ((tell $ here' String.++ ": overflow")))
          λ where
            {bs} (singleton read read≡) _ →
              subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength _ (n - x))) read≡
                (Option.parseOption₁ExactLength
                  TLV.nosubstrings
                  (tell $ here' String.++ ": underflow")
                  parseBitstring _))

parse : Parser (Logging ∘ Dec) Curve
parse = parseTLV _ here' _ parseFields

