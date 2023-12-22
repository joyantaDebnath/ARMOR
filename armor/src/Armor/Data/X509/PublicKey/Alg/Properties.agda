open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters
open import Armor.Data.X509.PublicKey.Alg.TCB
import      Armor.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
open import Armor.Data.X690-DER.Null
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.Sequence.DefinedByOID
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Sum
open import Armor.Prelude
open import Data.Sum.Properties

module Armor.Data.X509.PublicKey.Alg.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Sum         UInt8

@0 unambiguousParams : ∀ {@0 bs} → (o : OID bs) (o∈? : Dec ((-, TLV.val o) ∈ OIDs.Supported)) → Unambiguous (PKParameters' o o∈?)
unambiguousParams o (no ¬p) = OctetString.unambiguousValue
unambiguousParams o (yes (here px)) = Null.unambiguous
unambiguousParams o (yes (there (here px))) = ECPKParameters.unambiguous

@0 unambiguous : Unambiguous PublicKeyAlg
unambiguous =
  TLV.unambiguous
    (DefinedByOID.unambiguous PKParameters
      λ {bs} o → unambiguousParams o ((-, TLV.val o) ∈? OIDs.Supported))

@0 nonmalleableParams : NonMalleable₁ RawPKParameters
nonmalleableParams{bs}{o}{bs₁}{bs₂} =
  case (-, TLV.val o) ∈? OIDs.Supported
  ret (λ o∈? → (p₁ : PKParameters' o o∈? bs₁) (p₂ : PKParameters' o o∈? bs₂)
             → toRawPKParameters o o∈? p₁ ≡ toRawPKParameters o o∈? p₂
             → _≡_{A = Exists─ _ (PKParameters' o o∈?)} (─ bs₁ , p₁) (─ bs₂ , p₂))
  of λ where
    (no ¬p) p₁ p₂ eq → ‼ OctetString.nonmalleableValue p₁ p₂ (inj₁-injective eq)
    (yes (here px)) p₁ p₂ eq → ‼ Null.nonmalleable p₁ p₂ (inj₁-injective (inj₂-injective eq))
    (yes (there (here px))) p₁ p₂ eq → ‼ ECPKParameters.nonmalleable p₁ p₂ (inj₂-injective (inj₂-injective eq))

@0 nonmalleable : NonMalleable RawPublicKeyAlg
nonmalleable =
  DefinedByOID.nonmalleable PKParameters _ {RawPKParameters} λ {bs} {o} → nonmalleableParams{bs}{o}

