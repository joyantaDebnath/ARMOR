open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg
open import Armor.Data.X509.PublicKey.Alg.TCB.OIDs
open import Armor.Data.X509.PublicKey.Val
open import Armor.Data.X509.PublicKey.Properties
open import Armor.Data.X509.PublicKey.TCB
open import Armor.Data.X690-DER.OID.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ PublicKeyFields
  eq≋ =
    Iso.isoEq≋ iso
      (Seq.eq≋&ₚᵈ{A = PublicKeyAlg} (TLV.EqTLV ⦃ Alg.eq≋ ⦄) λ a → Val.eq≋{a = a})
