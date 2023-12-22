open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.TCB
import      Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.TCB.OIDs as OIDs
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.Sequence.DefinedByOID
import      Armor.Grammar.Definitions
open import Armor.Prelude
open import Data.Sum.Properties

module Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.Properties where

open Armor.Grammar.Definitions UInt8

@0 unambiguousParams : ∀ {@0 bs} → (o : OID bs) (o∈? : Dec ((-, TLV.val o) ∈ OIDs.Supported)) → Unambiguous (FieldIDParameters' o o∈?)
unambiguousParams o (no ¬p) = λ ()
unambiguousParams o (yes (here px)) = Int.unambiguous
unambiguousParams o (yes (there (here px))) = CharTwo.unambiguous

@0 unambiguous : Unambiguous FieldID
unambiguous =
  TLV.unambiguous
    (DefinedByOID.unambiguous FieldIDParameters
      λ {bs} o → unambiguousParams{bs} o ((-, TLV.val o) ∈? OIDs.Supported))

@0 nonmalleableParameters : NonMalleable₁ RawFieldIDParameters
nonmalleableParameters{bs}{o}{bs₁}{bs₂} =
  case (-, TLV.val o) ∈? OIDs.Supported
  ret (λ o∈? → (p₁ : FieldIDParameters' o o∈? bs₁) (p₂ : FieldIDParameters' o o∈? bs₂)
             → toRawFieldIDParameters o o∈? p₁ ≡ toRawFieldIDParameters o o∈? p₂
             → _≡_{A = Exists─ _ (FieldIDParameters' o o∈?)} (─ bs₁ , p₁) (─ bs₂ , p₂))
  of λ where
    (no ¬p) () _ _
    (yes (here px)) p₁ p₂ eq →
      ‼ Int.nonmalleable p₁ p₂ (inj₁-injective eq)
    (yes (there (here px))) p₁ p₂ eq → ‼ CharTwo.nonmalleable p₁ p₂ (inj₂-injective eq)

@0 nonmalleable : NonMalleable RawFieldID
nonmalleable = DefinedByOID.nonmalleable FieldIDParameters _ {R = RawFieldIDParameters} λ {bs}{a} → nonmalleableParameters{bs}{a} 

instance
  eq≋ : Eq≋ (DefinedByOIDFields FieldIDParameters)
  eq≋ = DefinedByOID.eq≋ FieldIDParameters λ {bs} o →
          case ((-, TLV.val o) ∈? OIDs.Supported)
          ret (λ o∈? → Eq≋ (FieldIDParameters' o o∈?))
          of λ where
            (no ¬p) → record { _≋?_ = λ ()}
            (yes (here px)) → it
            (yes (there (here px))) → it
