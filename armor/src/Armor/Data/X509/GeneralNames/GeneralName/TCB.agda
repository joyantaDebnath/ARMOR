open import Armor.Binary
open import Armor.Data.X509.Name.TCB
open import Armor.Data.X690-DER.OID.TCB
open import Armor.Data.X690-DER.OctetString.TCB
open import Armor.Data.X690-DER.Strings
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Sum.TCB
open import Armor.Prelude

module Armor.Data.X509.GeneralNames.GeneralName.TCB where

open      Armor.Grammar.Definitions              UInt8
open      Armor.Grammar.Sum.TCB                  UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.6
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

--- we do not support OtherName since very rarely used
OtherName : @0 List UInt8 → Set
OtherName xs = TLV Tag.AA0 OctetStringValue xs --abstracted

RfcName : @0 List UInt8 → Set
RfcName xs = TLV Tag.A81 IA5StringValue xs

DnsName : @0 List UInt8 → Set
DnsName xs = TLV Tag.A82 IA5StringValue xs

--- we do not support X400Address since very rarely used
X400Address : @0 List UInt8 → Set
X400Address xs = TLV Tag.AA3 OctetStringValue xs --abstracted

DirName : @0 List UInt8 → Set
DirName xs = TLV Tag.AA4 Name xs

--- we do not support EdipartyName since very rarely used
EdipartyName : @0 List UInt8 → Set
EdipartyName xs = TLV Tag.AA5 OctetStringValue xs --abstracted

URI : @0 List UInt8 → Set
URI xs = TLV Tag.A86 IA5StringValue xs

IpAddress : @0 List UInt8 → Set
IpAddress xs = TLV Tag.A87 OctetStringValue xs

RegID : @0 List UInt8 → Set
RegID xs = TLV Tag.A88 OIDValue xs

data GeneralName : @0 List UInt8 → Set where
  oname : ∀ {@0 bs} → OtherName bs → GeneralName bs
  rfcname : ∀ {@0 bs} → RfcName bs → GeneralName bs
  dnsname : ∀ {@0 bs} → DnsName bs → GeneralName bs
  x400add : ∀ {@0 bs} → X400Address bs → GeneralName bs
  dirname : ∀ {@0 bs} → DirName bs → GeneralName bs
  ediname : ∀ {@0 bs} → EdipartyName bs → GeneralName bs
  uri : ∀ {@0 bs} → URI bs → GeneralName bs
  ipadd : ∀ {@0 bs} → IpAddress bs → GeneralName bs
  rid : ∀ {@0 bs} → RegID bs → GeneralName bs

GeneralNameRep = Sum OtherName
                   (Sum RfcName
                     (Sum DnsName
                       (Sum X400Address
                         (Sum DirName
                           (Sum EdipartyName
                             (Sum URI
                               (Sum IpAddress RegID)))))))

equivalentGeneralName : Equivalent GeneralNameRep GeneralName
proj₁ equivalentGeneralName (inj₁ x) = oname x
proj₁ equivalentGeneralName (inj₂ (inj₁ x)) = rfcname x
proj₁ equivalentGeneralName (inj₂ (inj₂ (inj₁ x))) = dnsname x
proj₁ equivalentGeneralName (inj₂ (inj₂ (inj₂ (inj₁ x)))) = x400add x
proj₁ equivalentGeneralName (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))) = dirname x
proj₁ equivalentGeneralName (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))) = ediname x
proj₁ equivalentGeneralName (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))))) = uri x
proj₁ equivalentGeneralName (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))))) = ipadd x
proj₁ equivalentGeneralName (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ x)))))))) = rid x
proj₂ equivalentGeneralName (oname x) = inj₁ x
proj₂ equivalentGeneralName (rfcname x) = inj₂ (inj₁ x)
proj₂ equivalentGeneralName (dnsname x) = inj₂ (inj₂ (inj₁ x))
proj₂ equivalentGeneralName (x400add x) = inj₂ (inj₂ (inj₂ (inj₁ x)))
proj₂ equivalentGeneralName (dirname x) = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))
proj₂ equivalentGeneralName (ediname x) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))
proj₂ equivalentGeneralName (uri x) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))))
proj₂ equivalentGeneralName (ipadd x) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))))
proj₂ equivalentGeneralName (rid x) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ x)))))))

RawGeneralNameRep : Raw GeneralNameRep
RawGeneralNameRep =  RawSum (RawTLV _ RawOctetStringValue)
                    (RawSum (RawTLV _ RawIA5StringValue)
                    (RawSum (RawTLV _ RawIA5StringValue)
                    (RawSum (RawTLV _ RawOctetStringValue)
                    (RawSum (RawTLV _ RawName)
                    (RawSum (RawTLV _ RawOctetStringValue)
                    (RawSum (RawTLV _ RawIA5StringValue)
                    (RawSum (RawTLV _ RawOctetStringValue)
                            (RawTLV _ RawOIDValue))))))))

RawGeneralName : Raw GeneralName
RawGeneralName = Iso.raw equivalentGeneralName RawGeneralNameRep
