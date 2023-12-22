open import Armor.Binary
open import Armor.Data.X509.PublicKey.Val.RSA.Ints.Properties
open import Armor.Data.X509.PublicKey.Val.RSA.Ints.TCB
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Val.RSA.Ints.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ RSAPkIntsFields
  eq≋ =
    Iso.isoEq≋ iso (Eq⇒Eq≋ (Seq.eq&ₚ it it))
