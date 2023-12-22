open import Armor.Binary
open import Armor.Data.X690-DER.TLV.TCB
open import Armor.Data.X690-DER.BitString.TCB
open import Armor.Data.X690-DER.OctetString.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.Parallel.TCB
import      Armor.Grammar.Seq.TCB
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Val.EC.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8
open Armor.Grammar.Parallel.TCB             UInt8
open Armor.Grammar.Seq.TCB                  UInt8

{- https://datatracker.ietf.org/doc/html/rfc3279#section-2.3.5
 The elliptic curve public key (an ECPoint which is an OCTET STRING) is mapped
 to a subjectPublicKey (a BIT STRING) as follows: the most significant bit of
 the OCTET STRING becomes the most significant bit of the BIT STRING, and the
 least significant bit of the OCTET STRING becomes the least significant bit
 of the BIT STRING. Note that this octet string may represent an elliptic
 curve point in compressed or uncompressed form. Implementations that support
 elliptic curve according to this specification MUST support the uncompressed
 form and MAY support the compressed form.
-}

ECBitStringValue : @0 List UInt8 → Set
ECBitStringValue = &ₚ (λ x → Erased (x ≡ [ # 0 ])) OctetStringValue

RawECBitStringValue : Raw ECBitStringValue
RawECBitStringValue = Raw&ₚ RawSubSingleton RawOctetStringValue

ECBitString : @0 List UInt8 → Set
ECBitString = TLV Tag.BitString ECBitStringValue

RawECBitString : Raw ECBitString
RawECBitString = RawTLV _ RawECBitStringValue
