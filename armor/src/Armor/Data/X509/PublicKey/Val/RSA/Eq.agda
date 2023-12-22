open import Armor.Binary
open import Armor.Data.X509.PublicKey.Val.RSA.Ints
open import Armor.Data.X509.PublicKey.Val.RSA.Properties
open import Armor.Data.X509.PublicKey.Val.RSA.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Val.RSA.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ RSABitStringFields
  eq≋ =
    Iso.isoEq≋ iso
      (Eq⇒Eq≋
        (Seq.eq&ₚ
          (record
            { _≟_ = λ where
              (─ _ , ─ refl) (─ _ , ─ refl) → yes refl })
          (Eq≋⇒Eq it)))
