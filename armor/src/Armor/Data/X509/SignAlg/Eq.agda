open import Armor.Binary
open import Armor.Data.X509.HashAlg.RFC4055.TCB
open import Armor.Data.X509.SignAlg.TCB
import      Armor.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Armor.Data.X509.SignAlg.ECDSA
open import Armor.Data.X509.SignAlg.DSA
open import Armor.Data.X509.SignAlg.Properties
open import Armor.Data.X509.SignAlg.RSA
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.Int.TCB
open import Armor.Data.X690-DER.Null.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.OctetString.TCB
open import Armor.Data.X690-DER.Sequence.DefinedByOID
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Sum
open import Armor.Prelude
import      Data.List.Relation.Unary.Any.Properties as Any

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Sum         UInt8

module Armor.Data.X509.SignAlg.Eq where

instance
  eq≋ : Eq≋ (DefinedByOIDFields SignAlgParam)
  eq≋ =
    DefinedByOID.eq≋ SignAlgParam
      λ o →
        case isSupported o
        ret (λ o∈? → Eq≋ (SignAlgParam' o o∈?))
        of λ where
          (no ¬p) → it
          (yes p) →
            case lookupSignAlg o p
            ret (λ o∈ → Eq≋ (SignAlgParam“ o o∈))
            of λ where
              (inj₁ x) → record { _≋?_ = λ { (─ refl) (─ refl) → yes ≋-refl } }
              (inj₂ (inj₁ x)) → record { _≋?_ = λ { (─ refl) (─ refl) → yes ≋-refl } }
              (inj₂ (inj₂ y)) → RSA.eq≋Params'{o = o}{y}

  eq : Eq (Exists─ _ (DefinedByOIDFields SignAlgParam))
  eq = Eq≋⇒Eq it
