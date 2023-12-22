open import Armor.Binary
open import Armor.Data.X509.GeneralNames.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Prelude

module Armor.Data.X509.Extension.SAN.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.6
--    id-ce-subjectAltName OBJECT IDENTIFIER ::=  { id-ce 17 }

--    SubjectAltName ::= GeneralNames

--    GeneralNames ::= SEQUENCE SIZE (1..MAX) OF GeneralName

--    GeneralName ::= CHOICE {
--         otherName                       [0]     OtherName,
--         rfc822Name                      [1]     IA5String,
--         dNSName                         [2]     IA5String,
--         x400Address                     [3]     ORAddress,
--         directoryName                   [4]     Name,
--         ediPartyName                    [5]     EDIPartyName,
--         uniformResourceIdentifier       [6]     IA5String,
--         iPAddress                       [7]     OCTET STRING,
--         registeredID                    [8]     OBJECT IDENTIFIER }

--    OtherName ::= SEQUENCE {
--         type-id    OBJECT IDENTIFIER,
--         value      [0] EXPLICIT ANY DEFINED BY type-id }

--    EDIPartyName ::= SEQUENCE {
--         nameAssigner            [0]     DirectoryString OPTIONAL,
--         partyName               [1]     DirectoryString }
 
SANFields : @0 List UInt8 → Set
SANFields xs = TLV Tag.OctetString GeneralNames xs

RawSANFields : Raw SANFields
RawSANFields = RawTLV _ RawGeneralNames
