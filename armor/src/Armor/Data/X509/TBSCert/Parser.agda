open import Armor.Binary
open import Armor.Data.X509.Extension
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.PublicKey
open import Armor.Data.X509.Name
open import Armor.Data.X509.SignAlg
open import Armor.Data.X509.TBSCert.Properties
open import Armor.Data.X509.TBSCert.TCB
open import Armor.Data.X509.TBSCert.UID
open import Armor.Data.X509.TBSCert.Version
open import Armor.Data.X509.Validity
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.Default
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.Sequence
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X509.TBSCert.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

private
  here' = "X509: TBSCert"

parseTBSCertFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength TBSCertFields n)
parseTBSCertFields n =
  parseEquivalent equiv -- (Iso.transEquivalent (Iso.symEquivalent Distribute.exactLength-&) (Parallel.equivalent₁ equivalentTBSCertFields))
    (parse&ᵈ{A = Length≤ (&ₚ (Default [0]ExplicitVersion v1[0]ExplicitVersion) Int) n}
      (Parallel.nosubstrings₁ ns₁)
      (Parallel.Length≤.unambiguous _
        (Sequence.unambiguousDefault₁
          v1[0]ExplicitVersion Version.unambiguous[0]Explicit TLV.nosubstrings Int.unambiguous (TLV.noconfusion λ ())))
      (parse≤ _
        (Sequence.parseDefault₁{A = [0]ExplicitVersion} v1[0]ExplicitVersion here'
          Version.unambiguous[0]Explicit TLV.nosubstrings (TLV.noconfusion λ ())
          Version.parse[0]Explicit (Int.parse here'))
        ns₁ overflow)
      λ where
        (singleton r₁ r₁≡) _ →
          subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength Rep₇ (n - x)))
            r₁≡ (p₁ (n - r₁)))
  where
  equiv : Equivalent (&ₚᵈ (Length≤ (&ₚ (Default [0]ExplicitVersion v1[0]ExplicitVersion) Int) n) (λ {bs'} _ → ExactLength Rep₇ (n - length bs'))) (ExactLength TBSCertFields n)
  equiv = Iso.transEquivalent (Iso.symEquivalent Distribute.exactLength-&) (Parallel.equivalent₁ equivalentTBSCertFields)

  overflow : Logging (Level.Lift _ ⊤)
  overflow = tell $ here' String.++ ": overflow"

  @0 ns₁ : NoSubstrings (&ₚ (Default [0]ExplicitVersion v1[0]ExplicitVersion) Int)
  ns₁ = Sequence.nosubstringsDefault₁ v1[0]ExplicitVersion TLV.nosubstrings TLV.nosubstrings (TLV.noconfusion λ ())

  p₆ : ∀ n → Parser (Logging ∘ Dec) (ExactLength Rep₂ n)
  p₆ n =
      parse₂Option₃{A = IssUID}{B = SubUID}{C = Extensions}
        here'
        TLV.nosubstrings TLV.nosubstrings TLV.nosubstrings
        (TLV.noconfusion λ ()) (TLV.noconfusion λ ()) (TLV.noconfusion λ ())
        parseIssUID parseSubUID parseExtensions
        _

  p₅ : ∀ n → Parser (Logging ∘ Dec) (ExactLength Rep₃ n)
  p₅ n =
    parseEquivalent (Iso.symEquivalent Distribute.exactLength-&)
      (parse&ᵈ {A = Length≤ (PublicKey ×ₚ Singleton) n}
        (Parallel.nosubstrings₁ (Parallel.nosubstrings₁ TLV.nosubstrings))
        (Parallel.Length≤.unambiguous _ (Parallel.unambiguous×ₚ PublicKey.unambiguous (λ where self self → refl)))
        (parse≤ _ (parse×Singleton PublicKey.parse)
        (Parallel.nosubstrings₁ TLV.nosubstrings) overflow)
        λ where
          (singleton r r≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength Rep₂ (n - x)))
              r≡ (p₆ (n - r)))

  p₄ : ∀ n → Parser (Logging ∘ Dec) (ExactLength Rep₄ n)
  p₄ n =
    parseEquivalent (Iso.symEquivalent Distribute.exactLength-&)
      (parse&ᵈ {A = Length≤ Name n}
        (Parallel.nosubstrings₁ TLV.nosubstrings)
        (Parallel.Length≤.unambiguous _ Name.unambiguous)
        (parse≤ _ Name.parse TLV.nosubstrings overflow)
        λ where
          (singleton r r≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength Rep₃ (n ∸ x)))
              r≡
              (p₅ (n - r)))

  p₃ : ∀ n → Parser (Logging ∘ Dec) (ExactLength Rep₅ n)
  p₃ n =
    parseEquivalent (Iso.symEquivalent Distribute.exactLength-&)
      (parse&ᵈ {A = Length≤ Validity n}
        (Parallel.nosubstrings₁ TLV.nosubstrings)
        (Parallel.Length≤.unambiguous _ Validity.unambiguous)
        (parse≤ _ parseValidity TLV.nosubstrings overflow)
        λ where
          (singleton r r≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength Rep₄ (n ∸ x)))
              r≡ (p₄ (n - r)))

  p₂ : ∀ n → Parser (Logging ∘ Dec) (ExactLength Rep₆ n)
  p₂ n  =
    parseEquivalent (Iso.symEquivalent Distribute.exactLength-&)
      (parse&ᵈ{A = Length≤ Name n}
        (Parallel.nosubstrings₁ TLV.nosubstrings)
        (Parallel.Length≤.unambiguous _ Name.unambiguous)
        (parse≤ _ Name.parse TLV.nosubstrings overflow)
        λ where
          (singleton r r≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength Rep₅ (n ∸ x)))
              r≡ (p₃ (n - r)))

  p₁ : ∀ n → Parser (Logging ∘ Dec) (ExactLength Rep₇ n)
  p₁ n =
    parseEquivalent (Iso.symEquivalent Distribute.exactLength-&)
      (parse&ᵈ{A = Length≤ SignAlg n}
        (Parallel.nosubstrings₁{A = SignAlg} SignAlg.nosubstrings)
        (Parallel.Length≤.unambiguous _ SignAlg.unambiguous)
        (parse≤ _ SignAlg.parse SignAlg.nosubstrings overflow)
        λ where
          (singleton r r≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength Rep₆ (n - x)))
              r≡ (p₂ (n - r)))

parseTBSCert : Parser (Logging ∘ Dec) TBSCert
parseTBSCert = parseTLV _ here' _ parseTBSCertFields
