open import Armor.Binary
open import Armor.Data.X509.Extension.NC.GeneralSubtree.Properties
open import Armor.Data.X509.Extension.NC.GeneralSubtree.TCB
open import Armor.Data.X509.GeneralNames.GeneralName
open import Armor.Data.X690-DER.Default
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.Sequence
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.NC.GeneralSubtree.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.IList       UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

private
  here' = "X509: Extension: NC: GeneralSubtree"

parseExactLengthGeneralSubtrees : (n : ℕ) → Parser (Logging ∘ Dec) (ExactLength (GeneralSubtrees) n)
parseExactLengthGeneralSubtrees n =
  parseIListNonEmpty (tell $ here' String.++ ": underflow")
    _ TLV.nonempty TLV.nosubstrings
      (parseTLV _ here' _ helper) n
  where
  B = &ₚ (Default MinBaseDistance defaultMinBaseDistance) (Option MaxBaseDistance)
  equiv
    : ∀ n
      → Equivalent
          (&ₚᵈ (Length≤ GeneralName n) (λ {bs} _ → ExactLength B (n - length bs)))
           (ExactLength GeneralSubtreeFields n)
  equiv n =
    (Iso.transEquivalent
      (Iso.symEquivalent Distribute.exactLength-&)
      (Parallel.equivalent₁ equivalentGeneralSubtreeFields))

  p₂ : {@0 bs : List UInt8} → Singleton (length bs) → ∀ n → Parser (Logging ∘ Dec) (ExactLength B (n - length bs))
  p₂ (singleton r r≡) n =
    subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength B (n - x)))
      r≡
      (Sequence.parseDefaultOption _ here'
        Int.[ _ ]unambiguous TLV.nosubstrings
        TLV.nosubstrings (TLV.noconfusion λ ())
        (Int.[_]parse (here' String.++ ": MinBaseDistance") _)
        (Int.[_]parse (here' String.++ ": MaxBaseDistnace") _)
        (n - r))

  helper : (n : ℕ) → Parser (Logging ∘ Dec) (ExactLength (GeneralSubtreeFields) n)
  helper n =
    parseEquivalent (equiv n)
      (parse&ᵈ
        (Parallel.nosubstrings₁ GeneralName.nosubstrings)
        (Parallel.Length≤.unambiguous _ GeneralName.unambiguous)
        (parse≤ n parseGeneralName GeneralName.nosubstrings (tell $ here' String.++ ": underflow"))
        λ {bs} s a → p₂{bs} s n)
