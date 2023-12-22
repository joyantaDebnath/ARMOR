open import Armor.Binary
import      Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.Basis.TCB.OIDs as OIDs
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.Basis.TCB
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.Null
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.Sequence.DefinedByOID
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
open import Armor.Prelude
open import Data.Sum.Properties

module Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.Basis.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Seq         UInt8

@0 nosubstrings : NoSubstrings BasisFields
nosubstrings =
  DefinedByOID.nosubstrings BasisParameters
    λ o → ns o ((-, TLV.val o) ∈? OIDs.Supported)
  where
  ns : ∀ {@0 bs} (o : OID bs) (o∈? : Dec ((-, TLV.val o) ∈ OIDs.Supported)) → NoSubstrings (BasisParameters' o o∈?)
  ns o (no ¬p) = λ _ ()
  ns o (yes (here px)) = TLV.nosubstrings
  ns o (yes (there (here px))) = TLV.nosubstrings
  ns o (yes (there (there (here px)))) = Seq.nosubstrings TLV.nosubstrings (Seq.nosubstrings TLV.nosubstrings TLV.nosubstrings)

@0 unambiguous : Unambiguous BasisFields
unambiguous =
  DefinedByOID.unambiguous BasisParameters
    λ o →
      case (-, TLV.val o) ∈? OIDs.Supported
      ret (λ d → ∀ {@0 bs'} → (a₁ a₂ : BasisParameters' o d bs') → a₁ ≡ a₂)
      of λ where
        (yes (here px)) a₁ a₂ → ‼ Null.unambiguous a₁ a₂
        (yes (there (here px))) a₁ a₂ → ‼ Int.unambiguous a₁ a₂
        (yes (there (there (here px)))) a₁ a₂ →
          ‼ (Seq.unambiguous Int.unambiguous TLV.nosubstrings
            (Seq.unambiguous Int.unambiguous TLV.nosubstrings Int.unambiguous)
            a₁ a₂)

private
  @0 nonmalleablePentanomial : NonMalleable RawPentanomial
  nonmalleablePentanomial = Seq.nonmalleable Int.nonmalleable (Seq.nonmalleable Int.nonmalleable Int.nonmalleable)

@0 nonmalleableParameters : NonMalleable₁ RawBasisParameters
nonmalleableParameters{bs}{o}{bs₁}{bs₂} =
  case ((-, TLV.val o) ∈? OIDs.Supported)
  ret (λ o∈? → (p₁ : BasisParameters' o o∈? bs₁) (p₂ : BasisParameters' o o∈? bs₂)
             → toRawBasisParameters o o∈? p₁ ≡ toRawBasisParameters o o∈? p₂
             → _≡_{A = Exists─ (List UInt8) (BasisParameters' o o∈?)} (─ bs₁ , p₁) (─ bs₂ , p₂))
  of λ where
    (yes (here px)) p₁ p₂ eq →
      ‼ Null.nonmalleable p₁ p₂ (inj₁-injective eq)
    (yes (there (here px))) p₁ p₂ eq →
      ‼ Int.nonmalleable p₁ p₂ (inj₁-injective (inj₂-injective eq))
    (yes (there (there (here px)))) p₁ p₂ eq →
      ‼ nonmalleablePentanomial p₁ p₂ (inj₂-injective (inj₂-injective eq))

@0 nonmalleable : NonMalleable RawBasisFields
nonmalleable = DefinedByOID.nonmalleableFields BasisParameters{R = RawBasisParameters} λ {bs} {a} → nonmalleableParameters{bs}{a}

instance
  eq≋ : Eq≋ BasisFields
  eq≋ = DefinedByOID.eq≋ BasisParameters λ o →
          case (-, TLV.val o) ∈? OIDs.Supported
          ret (λ o∈? → Eq≋ (BasisParameters' o o∈?))
          of λ where
            (no ¬p) → record { _≋?_ = λ () }
            (yes (here px)) → it
            (yes (there (here px))) → it
            (yes (there (there (here px)))) →
              Seq.eq≋&ₚ it (Seq.eq≋&ₚ it it)
