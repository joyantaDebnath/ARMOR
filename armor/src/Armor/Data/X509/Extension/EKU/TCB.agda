open import Armor.Binary
open import Armor.Data.X690-DER.OID.TCB
open import Armor.Data.X690-DER.SequenceOf.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import Armor.Grammar.Definitions
open import Armor.Data.X690-DER.SequenceOf.TCB
open import Armor.Prelude

module Armor.Data.X509.Extension.EKU.TCB where

open Armor.Grammar.Definitions UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.12
--    id-ce-extKeyUsage OBJECT IDENTIFIER ::= { id-ce 37 }

--    ExtKeyUsageSyntax ::= SEQUENCE SIZE (1..MAX) OF KeyPurposeId

--    KeyPurposeId ::= OBJECT IDENTIFIER

EKUFieldsSeq : @0 List UInt8 → Set
EKUFieldsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf OID) xs

EKUFields : @0 List UInt8 → Set
EKUFields xs = TLV Tag.OctetString EKUFieldsSeq xs

RawEKUFields : Raw EKUFields
RawEKUFields = RawTLV _ (RawTLV _ (RawBoundedSequenceOf RawOID 1))
