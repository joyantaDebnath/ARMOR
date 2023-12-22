open import Armor.Binary
open import Armor.Data.X509.PublicKey.Val.EC.TCB
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel   
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Val.EC.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Seq         UInt8

@0 unambiguous : Unambiguous ECBitString
unambiguous =
  TLV.unambiguous
    (Seq.unambiguous (erased-unique ≡-unique) (λ where _ (─ refl) (─ refl) → refl) OctetString.unambiguousValue)

@0 nonmalleable : NonMalleable RawECBitString
nonmalleable =
  TLV.nonmalleable
    (Seq.nonmalleable
      (subsingleton⇒nonmalleable (λ where (─ _ , ─ refl) (─ _ , ─ refl) → refl))
      OctetString.nonmalleableValue)
