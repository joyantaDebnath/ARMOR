open import Armor.Binary
open import Armor.Data.X509.Extension.AIA.AccessDesc.TCB
open import Armor.Data.X690-DER.SequenceOf.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import Armor.Grammar.Definitions
open import Armor.Prelude

module Armor.Data.X509.Extension.AIA.TCB where

open Armor.Grammar.Definitions UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.2.1
--    id-pe-authorityInfoAccess OBJECT IDENTIFIER ::= { id-pe 1 }

--    AuthorityInfoAccessSyntax  ::=
--            SEQUENCE SIZE (1..MAX) OF AccessDescription

--    AccessDescription  ::=  SEQUENCE {
--            accessMethod          OBJECT IDENTIFIER,
--            accessLocation        GeneralName  }

--    id-ad OBJECT IDENTIFIER ::= { id-pkix 48 }

--    id-ad-caIssuers OBJECT IDENTIFIER ::= { id-ad 2 }

--    id-ad-ocsp OBJECT IDENTIFIER ::= { id-ad 1 }
           
AIAFieldsSeq : @0 List UInt8 → Set
AIAFieldsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf AccessDesc) xs

AIAFields : @0 List UInt8 → Set
AIAFields xs = TLV Tag.OctetString AIAFieldsSeq xs

RawAIAFields : Raw AIAFields
RawAIAFields = RawTLV _ (RawTLV _ (RawBoundedSequenceOf RawAccessDesc 1))
