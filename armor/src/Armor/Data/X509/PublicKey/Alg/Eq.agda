open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg.TCB
import      Armor.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters
open import Armor.Data.X509.PublicKey.Alg.RSAPKParameters
open import Armor.Data.X690-DER.Null
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.Sequence.DefinedByOID
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Sum
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Alg.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Sum         UInt8

instance
  eq≋ : Eq≋ (DefinedByOIDFields PKParameters)
  eq≋ =
    DefinedByOID.eq≋ PKParameters
      λ {bs} o →
        case (-, TLV.val o) ∈? OIDs.Supported
        ret (λ o∈? → Eq≋ (PKParameters' o o∈?))
        of λ where
          (no ¬p) → it
          (yes (here px)) → it
          (yes (there (here px))) → it
