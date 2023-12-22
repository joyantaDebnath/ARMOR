open import Armor.Binary
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.Sequence.DefinedByOID.TCB
open import Armor.Data.X690-DER.Sequence.DefinedByOID.Properties
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X690-DER.Sequence.DefinedByOID.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

private
  here' = "Sequence: DefinedByOID"

parseFields
  : ∀ {P : ∀ {@0 bs} → OID bs → @0 List UInt8 → Set}
    → (s : String)
    → (∀ n {@0 bs} → (o : OID bs) → Parser (Logging ∘ Dec) (ExactLength (P o) n))
    → ∀ n → Parser (Logging ∘ Dec) (ExactLength (DefinedByOIDFields P) n)
parseFields{P} s p₁ n =
  parseEquivalent
    (Iso.transEquivalent{B = ExactLength (DefinedByOIDFieldsRep P) n}
      (Iso.symEquivalent Distribute.exactLength-&ᵈ)
      (Parallel.equivalent₁ (equivalent{P})))
    (parse&ᵈ
      (Parallel.nosubstrings₁ TLV.nosubstrings)
      (Parallel.Length≤.unambiguous _ OID.unambiguous)
      (parse≤ _ parseOID TLV.nosubstrings (tell $ s String.++ here' String.++ " (fields): overflow (OID)"))
      λ where
        (singleton r r≡) (mk×ₚ a (─ r≤)) →
          let p = p₁ (n - r) a in
          subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength (P a) (n - x))) r≡ p)

parse
  : ∀ {P : ∀ {@0 bs} → OID bs → @0 List UInt8 → Set}
    → String
    → (∀ n {@0 bs} → (o : OID bs) → Parser (Logging ∘ Dec) (ExactLength (P o) n))
    → Parser (Logging ∘ Dec) (DefinedByOID P)
parse{P} s p = parseTLV _ (s String.++ here') (DefinedByOIDFields P) λ n → parseFields s p n
