open import Armor.Binary
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.SequenceOf.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
open import Armor.Prelude

module Armor.Data.X509.Extension.CertPolicy.TCB where

open      Armor.Grammar.Definitions              UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.4
--    id-ce-certificatePolicies OBJECT IDENTIFIER ::=  { id-ce 32 }

--    anyPolicy OBJECT IDENTIFIER ::= { id-ce-certificatePolicies 0 }

--    certificatePolicies ::= SEQUENCE SIZE (1..MAX) OF PolicyInformation

--    PolicyInformation ::= SEQUENCE {
--         policyIdentifier   CertPolicyId,
--         policyQualifiers   SEQUENCE SIZE (1..MAX) OF
--                                 PolicyQualifierInfo OPTIONAL }

--    CertPolicyId ::= OBJECT IDENTIFIER

--    PolicyQualifierInfo ::= SEQUENCE {
--         policyQualifierId  PolicyQualifierId,
--         qualifier          ANY DEFINED BY policyQualifierId }

--    -- policyQualifierIds for Internet policy qualifiers

--    id-qt          OBJECT IDENTIFIER ::=  { id-pkix 2 }
--    id-qt-cps      OBJECT IDENTIFIER ::=  { id-qt 1 }
--    id-qt-unotice  OBJECT IDENTIFIER ::=  { id-qt 2 }

--    PolicyQualifierId ::= OBJECT IDENTIFIER ( id-qt-cps | id-qt-unotice )

--    Qualifier ::= CHOICE {
--         cPSuri           CPSuri,
--         userNotice       UserNotice }

--    CPSuri ::= IA5String

--    UserNotice ::= SEQUENCE {
--         noticeRef        NoticeReference OPTIONAL,
--         explicitText     DisplayText OPTIONAL }

--    NoticeReference ::= SEQUENCE {
--         organization     DisplayText,
--         noticeNumbers    SEQUENCE OF INTEGER }

--    DisplayText ::= CHOICE {
--         ia5String        IA5String      (SIZE (1..200)),
--         visibleString    VisibleString  (SIZE (1..200)),
--         bmpString        BMPString      (SIZE (1..200)),
--         utf8String       UTF8String     (SIZE (1..200)) }

CertPolFieldsSeq : @0 List UInt8 → Set
CertPolFieldsSeq = TLV Tag.Sequence (NonEmptySequenceOf PolicyInformation)

CertPolFields : @0 List UInt8 → Set
CertPolFields xs = TLV Tag.OctetString  CertPolFieldsSeq xs

RawCertPolFields : Raw CertPolFields
RawCertPolFields = RawTLV _ (RawTLV _ (RawBoundedSequenceOf RawPolicyInformation 1))
