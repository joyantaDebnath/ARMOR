open import Armor.Binary
open import Armor.Data.X509.PublicKey.Val.EC.TCB
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Val.EC.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ ECBitStringValue
  eq≋ = Seq.eq≋&ₚ (record { _≋?_ = λ where (─ refl) (─ refl) → yes ≋-refl }) it
