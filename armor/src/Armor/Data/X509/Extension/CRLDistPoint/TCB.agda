open import Armor.Binary
open import Armor.Data.X509.GeneralNames.TCB
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.TCB
open import Armor.Data.X690-DER.SequenceOf.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
open import Armor.Prelude

module Armor.Data.X509.Extension.CRLDistPoint.TCB where

open Armor.Grammar.Definitions UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.13
--    id-ce-cRLDistributionPoints OBJECT IDENTIFIER ::=  { id-ce 31 }

--    CRLDistributionPoints ::= SEQUENCE SIZE (1..MAX) OF DistributionPoint

--    DistributionPoint ::= SEQUENCE {
--         distributionPoint       [0]     DistributionPointName OPTIONAL,
--         reasons                 [1]     ReasonFlags OPTIONAL,
--         cRLIssuer               [2]     GeneralNames OPTIONAL }

--    DistributionPointName ::= CHOICE {
--         fullName                [0]     GeneralNames,
--         nameRelativeToCRLIssuer [1]     RelativeDistinguishedName }

--    ReasonFlags ::= BIT STRING {
--         unused                  (0),
--         keyCompromise           (1),
--         cACompromise            (2),
--         affiliationChanged      (3),
--         superseded              (4),
--         cessationOfOperation    (5),
--         certificateHold         (6),
--         privilegeWithdrawn      (7),
--         aACompromise            (8) }
        
CRLDistFieldsSeq : @0 List UInt8 → Set
CRLDistFieldsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf DistPoint) xs

CRLDistFields : @0 List UInt8 → Set
CRLDistFields xs = TLV Tag.OctetString  CRLDistFieldsSeq xs

RawCRLDistFields : Raw CRLDistFields
RawCRLDistFields = RawTLV _ (RawTLV _ (RawBoundedSequenceOf RawDistPoint 1))
