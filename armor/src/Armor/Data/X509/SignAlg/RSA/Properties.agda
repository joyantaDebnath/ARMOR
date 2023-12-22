open import Armor.Binary
import      Armor.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Armor.Data.X509.SignAlg.RSA.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.Sequence.DefinedByOID
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.Null
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Prelude
open import Data.Sum.Properties

module Armor.Data.X509.SignAlg.RSA.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

@0 unambiguous : Unambiguous RSA
unambiguous =
  TLV.unambiguous
    (DefinedByOID.unambiguous RSAParams
      λ {bs} o →
        case (-, TLV.val o) ∈? OIDs.RSA.Supported
        ret (λ o∈? → Unambiguous (RSAParams' o o∈?))
        of λ where
          (no ¬p) → λ ()
          (yes (here px)) a₁ a₂ →
            ‼ Null.unambiguous a₁ a₂
          (yes (there (here px))) a₁ a₂ →
            ‼ Null.unambiguous a₁ a₂
          (yes (there (there (here px)))) a₁ a₂ →
            ‼ Null.unambiguous a₁ a₂
          (yes (there (there (there (here px))))) a₁ a₂ →
            ‼ Option.unambiguous Null.unambiguous TLV.nonempty a₁ a₂
          (yes (there (there (there (there (here px)))))) a₁ a₂ →
            ‼ Option.unambiguous Null.unambiguous TLV.nonempty a₁ a₂
          (yes (there (there (there (there (there (here px))))))) a₁ a₂ →
            ‼ Option.unambiguous Null.unambiguous TLV.nonempty a₁ a₂
          (yes (there (there (there (there (there (there (here px)))))))) a₁ a₂ →
            ‼ Option.unambiguous Null.unambiguous TLV.nonempty a₁ a₂
          (yes (there (there (there (there (there (there (there (here px))))))))) a₁ a₂ →
            ‼ TLV.unambiguous OctetString.unambiguousValue a₁ a₂)

@0 nonmalleable : NonMalleable RawRSA
nonmalleable =
  DefinedByOID.nonmalleable RSAParams _ {R = RawRSAParams}
    λ {bs} {a} → nm {bs} {a}
  where
  nm : NonMalleable₁ RawRSAParams
  nm{bs}{o}{bs₁}{bs₂} =
    case (-, TLV.val o) ∈? OIDs.RSA.Supported
    ret (λ o∈? → (p₁ : RSAParams' o o∈? bs₁) (p₂ : RSAParams' o o∈? bs₂)
               → toRawRSAParams' o o∈? p₁ ≡ toRawRSAParams' o o∈? p₂
               → _≡_{A = Exists─ _ (RSAParams' o o∈?)} (─ bs₁ , p₁) (─ bs₂ , p₂))
    of λ where
      (no ¬p) → λ ()
      (yes p) →
        (case splitRSA∈ o p
          ret (λ o∈? → (p₁ : RSAParams“ o o∈? bs₁) (p₂ : RSAParams“ o o∈? bs₂)
               → toRawRSAParams“ o o∈? p₁ ≡ toRawRSAParams“ o o∈? p₂
               → _≡_{A = Exists─ _ (RSAParams“ o o∈?)} (─ bs₁ , p₁) (─ bs₂ , p₂))
          of λ where
          (inj₁ x) p₁ p₂ x₁ → ‼ Null.nonmalleable  p₁ p₂ refl
          (inj₂ (inj₁ x)) p₁ p₂ x₁ → ‼ Option.nonmalleable RawNull Null.nonmalleable
            p₁ p₂ (inj₁-injective (inj₂-injective x₁))
          (inj₂ (inj₂ y)) p₁ p₂ refl → ‼ TLV.nonmalleable OctetString.nonmalleableValue p₁ p₂ refl)

eq≋Params' : ∀ {@0 bs} {o : OID bs} {o∈ : (-, TLV.val o) ∈ OIDs.RSA.Supported} → Eq≋ (RSAParams“ o (splitRSA∈ o o∈))
eq≋Params'{o = o}{o∈} =
  case splitRSA∈ o o∈
  ret (λ x → Eq≋ (RSAParams“ o x))
  of λ where
    (inj₁ x) → it
    (inj₂ (inj₁ x)) → it
    (inj₂ (inj₂ y)) → it
