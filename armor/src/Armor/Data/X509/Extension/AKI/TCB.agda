open import Armor.Binary
open import Armor.Data.X509.GeneralNames.TCB
open import Armor.Data.X690-DER.Int.TCB
open import Armor.Data.X690-DER.OctetString.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Seq.TCB
open import Armor.Prelude

module Armor.Data.X509.Extension.AKI.TCB where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option UInt8
open Armor.Grammar.Seq.TCB UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.1
--    id-ce-authorityKeyIdentifier OBJECT IDENTIFIER ::=  { id-ce 35 }

--    AuthorityKeyIdentifier ::= SEQUENCE {
--       keyIdentifier             [0] KeyIdentifier           OPTIONAL,
--       authorityCertIssuer       [1] GeneralNames            OPTIONAL,
--       authorityCertSerialNumber [2] CertificateSerialNumber OPTIONAL  }

--    KeyIdentifier ::= OCTET STRING
   
AKIKeyId : @0 List UInt8 → Set
AKIKeyId = TLV Tag.A80 OctetStringValue

AKIAuthCertIssuer : @0 List UInt8 → Set
AKIAuthCertIssuer = TLV Tag.AA1 GeneralNamesElems

AKIAuthCertSN : @0 List UInt8 → Set
AKIAuthCertSN = [ Tag.A82 ]Int

record AKIFieldsSeqFields (@0 bs : List UInt8) : Set where
  constructor mkAKIFieldsSeqFields
  field
    @0 {akid ci csn} : List UInt8
    akeyid : Option AKIKeyId akid
    authcertiss : Option AKIAuthCertIssuer ci
    authcertsn : Option AKIAuthCertSN csn
    @0 bs≡  : bs ≡ akid ++ ci ++ csn

AKIFieldsSeq : @0 List UInt8 → Set
AKIFieldsSeq = TLV Tag.Sequence AKIFieldsSeqFields

AKIFields : @0 List UInt8 → Set
AKIFields = TLV Tag.OctetString AKIFieldsSeq

AKIFieldsSeqFieldsRep = &ₚ (Option AKIKeyId) (&ₚ (Option AKIAuthCertIssuer) (Option AKIAuthCertSN))

equivalentAKIFieldsSeqFields : Equivalent AKIFieldsSeqFieldsRep AKIFieldsSeqFields
proj₁ equivalentAKIFieldsSeqFields (mk&ₚ v₁ (mk&ₚ v₂ v₃ refl) refl) = mkAKIFieldsSeqFields v₁ v₂ v₃ refl
proj₂ equivalentAKIFieldsSeqFields (mkAKIFieldsSeqFields v₁ v₂ v₃ refl) = mk&ₚ v₁ (mk&ₚ v₂ v₃ refl) refl

RawAKIFieldsSeqFieldsRep : Raw AKIFieldsSeqFieldsRep
RawAKIFieldsSeqFieldsRep =  Raw&ₚ (RawOption (RawTLV _ RawOctetStringValue))
                          (Raw&ₚ (RawOption (RawTLV _ RawGeneralNamesElems))
                                  (RawOption (RawTLV _ RawIntegerValue)))

RawAKIFieldsSeqFields : Raw AKIFieldsSeqFields
RawAKIFieldsSeqFields = Iso.raw equivalentAKIFieldsSeqFields RawAKIFieldsSeqFieldsRep

RawAKIFields : Raw AKIFields
RawAKIFields = RawTLV _ (RawTLV _ RawAKIFieldsSeqFields)
