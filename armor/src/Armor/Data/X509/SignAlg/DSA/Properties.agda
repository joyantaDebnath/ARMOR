open import Armor.Binary
open import Armor.Data.X509.SignAlg.DSA.TCB
import      Armor.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.Sequence.DefinedByOID
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
open import Armor.Prelude

module Armor.Data.X509.SignAlg.DSA.Properties where

open Armor.Grammar.Definitions UInt8

@0 unambiguous : Unambiguous DSA
unambiguous =
  TLV.unambiguous
    (DefinedByOID.unambiguous DSAParams
      λ {bs} o →
        case (-, TLV.val o) ∈? OIDs.DSA.Supported
        ret (λ o∈? → Unambiguous (DSAParams' o o∈?))
        of λ where
          (no ¬p) → λ ()
          (yes p) → erased-unique ≡-unique)

@0 nonmalleable : NonMalleable RawDSA
nonmalleable =
  DefinedByOID.nonmalleable DSAParams _ {R = RawDSAParams}
    λ {bs} {a} → nm {bs} {a}
  where
  nm : NonMalleable₁ RawDSAParams
  nm{bs}{o}{bs₁}{bs₂} =
    case (-, TLV.val o) ∈? OIDs.DSA.Supported
    ret (λ o∈? → (p₁ : DSAParams' o o∈? bs₁) (p₂ : DSAParams' o o∈? bs₂)
               → toRawDSAParams o o∈? p₁ ≡ toRawDSAParams o o∈? p₂
               → _≡_{A = Exists─ _ (DSAParams' o o∈?)} (─ bs₁ , p₁) (─ bs₂ , p₂))
    of λ where
      (no ¬p) → λ ()
      (yes p) → λ where (─ refl) (─  refl) _ → refl
