open import Armor.Data.X690-DER.OID.TCB
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.TLV
open import Armor.Prelude

module Armor.Data.X690-DER.OID.Serializer where

serializeSub : ∀ {@0 bs} → OIDSub bs → Singleton bs
serializeSub (mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 leastDigs bs≡) =
  singleton _ (sym bs≡)

serializeVal : ∀ {@0 bs} → OIDValue bs → Singleton bs
serializeVal = serializeNonEmptySequenceOf serializeSub

serialize : ∀ {@0 bs} → OID bs → Singleton bs
serialize = TLV.serialize serializeVal
