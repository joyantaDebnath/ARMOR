open import Armor.Binary
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Properties
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.SequenceOf
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

private
  here' = "X509: Extension: CertPolicy: PolicyInformation"

open ≡-Reasoning

parsePolicyInformationFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength PolicyInformationFields n)
parsePolicyInformationFields n =
  parseEquivalent{A = &ₚᵈ (Length≤ OID n) (λ {bs} _ → ExactLength (Option PolicyQualifiersSeq) (n - length bs))}
    (Iso.transEquivalent (Iso.symEquivalent Distribute.exactLength-&) (Parallel.equivalent₁ equivalentPolicyInformationFields))
    (parse&ᵈ
      (Parallel.nosubstrings₁ TLV.nosubstrings)
      (Parallel.Length≤.unambiguous _ OID.unambiguous)
      (parse≤ _ parseOID TLV.nosubstrings (tell $ here' String.++ ": overflow"))
      λ where
        (singleton r r≡) _ →
          subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength (Option PolicyQualifiersSeq) (n - x)))
            r≡
            (Option.parseOption₁ExactLength TLV.nosubstrings
              (tell $ here' String.++ ": underflow")
              parsePolicyQualifiersSeq (n - r)))
        
parsePolicyInformation : Parser (Logging ∘ Dec) PolicyInformation
parsePolicyInformation =
  parseTLV _ here' _ parsePolicyInformationFields

