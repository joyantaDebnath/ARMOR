open import Armor.Binary
open import Armor.Data.X690-DER.OctetString.TCB
open import Armor.Data.X690-DER.Int.TCB
open import Armor.Data.X690-DER.Length
open import Armor.Data.X690-DER.Null.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.Sequence.DefinedByOID
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.Null
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X509.HashAlg.RFC4055
-- open import Armor.Data.X509.SignAlg.Exclusions
open import Armor.Data.X509.SignAlg.TCB
import      Armor.Data.X509.SignAlg.TCB.OIDs          as OIDs
import      Armor.Data.X509.SignAlg.ECDSA.TCB         as ECDSA
import      Armor.Data.X509.SignAlg.ECDSA.Properties  as ECDSA
import      Armor.Data.X509.SignAlg.DSA.Properties    as DSA
import      Armor.Data.X509.SignAlg.DSA.TCB           as DSA
import      Armor.Data.X509.SignAlg.RSA.Properties    as RSA
import      Armor.Data.X509.SignAlg.RSA.TCB           as RSA
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Properties
import      Armor.Grammar.Sum
import      Armor.Grammar.Option
open import Armor.Prelude
import      Data.List.Relation.Unary.Any.Properties as Any
open import Data.Sum.Properties
open import Relation.Nullary.Negation
  using (¬?)

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Sum         UInt8
open Armor.Grammar.Option      UInt8

module Armor.Data.X509.SignAlg.Properties where

@0 nosubstrings : NoSubstrings SignAlg
nosubstrings = TLV.nosubstrings

@0 unambiguous : Unambiguous SignAlg
unambiguous =
  TLV.unambiguous
    (DefinedByOID.unambiguous SignAlgParam
      λ {bs} o →
        case (-, TLV.val o) ∈? OIDs.Supported
        ret (λ o∈? → Unambiguous (SignAlgParam' o o∈?))
        of λ where
          (no ¬p) (singleton x refl) (singleton x₁ refl) → refl
          (yes p) →
            (case lookupSignAlg o p
              ret (λ o∈? → (p₁ : SignAlgParam“ o o∈? _) (p₂ : SignAlgParam“ o o∈? _) → p₁ ≡ p₂)
              of λ where
              (inj₁ x) → erased-unique ≡-unique
              (inj₂ (inj₁ x)) → erased-unique ≡-unique 
              (inj₂ (inj₂ y)) →
                (case RSA.splitRSA∈ o y
                ret (λ o∈? → (p₁ : RSA.RSAParams“ o o∈? _) (p₂ : RSA.RSAParams“ o o∈? _)
                  → _≡_ p₁ p₂)
                of λ
                where
                  (inj₁ x) p₁ p₂ → ‼ Null.unambiguous p₁ p₂
                  (inj₂ (inj₁ x)) p₁ p₂ → ‼ Option.unambiguous Null.unambiguous TLV.nonempty p₁ p₂
                  (inj₂ (inj₂ y)) p₁ p₂ → ‼ TLV.unambiguous OctetString.unambiguousValue p₁ p₂)))

@0 nonmalleable : NonMalleable RawSignAlg
nonmalleable =
  DefinedByOID.nonmalleable SignAlgParam _ {R = RawSignAlgParam}
    λ {bs} {a} → nm {bs} {a}
  where
  nm : NonMalleable₁ RawSignAlgParam
  nm{bs}{o}{bs₁}{bs₂} =
    case (-, TLV.val o) ∈? OIDs.Supported
    ret (λ o∈? → (p₁ : SignAlgParam' o o∈? bs₁) (p₂ : SignAlgParam' o o∈? bs₂)
               → toRawSignAlgParam' o o∈? p₁ ≡ toRawSignAlgParam' o o∈? p₂
               → _≡_{A = Exists─ _ (SignAlgParam' o o∈?)} (─ bs₁ , p₁) (─ bs₂ , p₂))
    of λ where
      (no ¬p) (singleton bytes₁ refl) (singleton bytes₂ refl) refl → refl
      (yes p) →
            (case lookupSignAlg o p
              ret (λ o∈? → (p₁ : SignAlgParam“ o o∈? bs₁) (p₂ : SignAlgParam“ o o∈? bs₂)
                → toRawSignAlgParam“ o o∈? p₁ ≡ toRawSignAlgParam“ o o∈? p₂
                → _≡_{A = Exists─ _ (SignAlgParam“ o o∈?)} (─ bs₁ , p₁) (─ bs₂ , p₂))
              of λ where
              (inj₁ x) → λ where (─ refl) (─  refl) _ → refl
              (inj₂ (inj₁ x)) → λ where (─ refl) (─  refl) _ → refl
              (inj₂ (inj₂ y)) →
                case RSA.splitRSA∈ o y
                ret (λ o∈? → (p₁ : RSA.RSAParams“ o o∈? bs₁) (p₂ : RSA.RSAParams“ o o∈? bs₂)
                  → inj₂ (inj₂ (inj₂ (RSA.toRawRSAParams“ o o∈? p₁))) ≡
                     inj₂ (inj₂ (inj₂ (RSA.toRawRSAParams“ o o∈? p₂)))
                  → _≡_{A = Exists─ _ (RSA.RSAParams“ o o∈?)} (─ bs₁ , p₁) (─ bs₂ , p₂))
                of λ where
                (inj₁ x) p₁ p₂ x₁ → ‼ Null.nonmalleable  p₁ p₂ refl
                (inj₂ (inj₁ x)) p₁ p₂ x₁ → ‼ Option.nonmalleable RawNull Null.nonmalleable
                  p₁ p₂ (inj₁-injective (inj₂-injective (inj₂-injective (inj₂-injective (inj₂-injective x₁)))))
                (inj₂ (inj₂ y)) p₁ p₂ refl → ‼ TLV.nonmalleable OctetString.nonmalleableValue p₁ p₂ refl)
