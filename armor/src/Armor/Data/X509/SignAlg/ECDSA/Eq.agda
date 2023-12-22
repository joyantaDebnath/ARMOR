open import Armor.Binary
open import Armor.Data.X509.SignAlg.ECDSA.TCB
import      Armor.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.Sequence.DefinedByOID
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
open import Armor.Prelude

module Armor.Data.X509.SignAlg.ECDSA.Eq where

open Armor.Grammar.Definitions UInt8

instance
  eq≋ : Eq≋ (DefinedByOIDFields ECDSAParams)
  eq≋ = DefinedByOID.eq≋ ECDSAParams λ o →
          case (-, TLV.val o) ∈? OIDs.ECDSA.Supported
          ret (λ o∈? → Eq≋ (ECDSAParams' o o∈?))
          of λ where
            (no ¬p) → record { _≋?_ = λ () }
            (yes p) → record { _≋?_ = λ where (─ refl) (─ refl) → yes ≋-refl }
