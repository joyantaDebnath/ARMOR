open import Armor.Binary
open import Armor.Data.X509.HashAlg.RFC4055.TCB
import      Armor.Data.X509.HashAlg.TCB.OIDs as OIDs
open import Armor.Data.X690-DER.Null
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.Sequence.DefinedByOID
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Prelude

module Armor.Data.X509.HashAlg.RFC4055.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

@0 unambiguous : Unambiguous HashAlg
unambiguous =
  TLV.unambiguous
    (DefinedByOID.unambiguous HashAlgParam
      (λ o →
        case (-, TLV.val o) ∈? OIDs.RFC4055
        ret (λ o∈? → Unambiguous (HashAlgParam' o o∈?))
        of λ where
          (yes p) a₁ a₂ → ‼ Option.unambiguous Null.unambiguous TLV.nonempty a₁ a₂))

@0 nonmalleable : NonMalleable RawHashAlg
nonmalleable =
  DefinedByOID.nonmalleable HashAlgParam _ {R = RawHashAlgParam}
    (λ {bs}{o}{bs₁}{bs₂} →
      case (-, TLV.val o) ∈? OIDs.RFC4055
      ret (λ o∈? → (p₁ : HashAlgParam' o o∈? bs₁) (p₂ : HashAlgParam' o o∈? bs₂)
                 → toRawHashAlgParam o o∈? p₁ ≡ toRawHashAlgParam o o∈? p₂
                 → _≡_{A = Exists─ _ (HashAlgParam' o o∈?)} (─ bs₁ , p₁) (─ bs₂ , p₂))
      of λ where
        (no ¬p) → λ ()
        (yes p) p₁ p₂ eq → ‼ (Option.nonmalleable RawNull Null.nonmalleable p₁ p₂ eq))

instance
  eq≋ : Eq≋ (DefinedByOIDFields HashAlgParam)
  eq≋ = DefinedByOID.eq≋ HashAlgParam λ o →
          case (-, TLV.val o) ∈? OIDs.RFC4055
          ret (λ x → Eq≋ (HashAlgParam' o x))
          of λ where
            (no ¬p) → record { _≋?_ = λ () }
            (yes p) → it
