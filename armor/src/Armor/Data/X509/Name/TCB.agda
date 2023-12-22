open import Armor.Binary
open import Armor.Data.X690-DER.SequenceOf.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X509.Name.RDN.TCB
import      Armor.Grammar.Definitions.NonMalleable.Base
open import Armor.Prelude

module Armor.Data.X509.Name.TCB where

open Armor.Grammar.Definitions.NonMalleable.Base UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.2.4
-- Name ::= CHOICE { -- only one possibility for now --
--   rdnSequence  RDNSequence }
--
-- RDNSequence ::= SEQUENCE OF RelativeDistinguishedName
--
-- RelativeDistinguishedName ::=
--   SET SIZE (1..MAX) OF AttributeTypeAndValue

Name : @0 List UInt8 → Set
Name = RDNSequence

RawName : Raw Name
RawName = RawRDNSequence
