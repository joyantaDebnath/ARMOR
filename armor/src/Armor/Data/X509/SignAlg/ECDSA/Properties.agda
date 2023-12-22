open import Armor.Binary
import      Armor.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Armor.Data.X509.SignAlg.ECDSA.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.Sequence.DefinedByOID
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
open import Armor.Prelude

module Armor.Data.X509.SignAlg.ECDSA.Properties where

open Armor.Grammar.Definitions UInt8

@0 unambiguous : Unambiguous ECDSA
unambiguous =
  TLV.unambiguous
    (DefinedByOID.unambiguous ECDSAParams
      λ {bs} o →
        case (-, TLV.val o) ∈? OIDs.ECDSA.Supported
        ret (λ o∈? → Unambiguous (ECDSAParams' o o∈?))
        of λ where
          (no ¬p) → λ ()
          (yes p) → erased-unique ≡-unique)

@0 nonmalleable : NonMalleable RawECDSA
nonmalleable =
  DefinedByOID.nonmalleable ECDSAParams _ {R = RawECDSAParams}
    λ {bs} {a} → nm {bs} {a}
  where
  nm : NonMalleable₁ RawECDSAParams
  nm{bs}{o}{bs₁}{bs₂} =
    case (-, TLV.val o) ∈? OIDs.ECDSA.Supported
    ret (λ o∈? → (p₁ : ECDSAParams' o o∈? bs₁) (p₂ : ECDSAParams' o o∈? bs₂)
               → toRawECDSAParams o o∈? p₁ ≡ toRawECDSAParams o o∈? p₂
               → _≡_{A = Exists─ _ (ECDSAParams' o o∈?)} (─ bs₁ , p₁) (─ bs₂ , p₂))
    of λ where
      (no ¬p) → λ ()
      (yes p) → λ where (─ refl) (─  refl) _ → refl
