open import Armor.Binary
open import Armor.Data.X690-DER.OID.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.SequenceOf.TCB
import      Armor.Grammar.Definitions
import Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.PM.TCB where

open  Armor.Grammar.Definitions              UInt8
open Armor.Grammar.Seq                       UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.5
--    id-ce-policyMappings OBJECT IDENTIFIER ::=  { id-ce 33 }

--    PolicyMappings ::= SEQUENCE SIZE (1..MAX) OF SEQUENCE {
--         issuerDomainPolicy      CertPolicyId,
--         subjectDomainPolicy     CertPolicyId }

record PolicyMapFields (@0 bs : List UInt8) : Set where
  constructor mkPolicyMapFields
  field
    @0 {iss sub} : List UInt8
    issuerDomainPolicy : OID iss
    subjectDomainPolicy : OID sub
    @0 bs≡  : bs ≡ iss ++ sub

PolicyMap : @0 List UInt8 → Set
PolicyMap xs = TLV Tag.Sequence PolicyMapFields xs

PMFieldsSeq : @0 List UInt8 → Set
PMFieldsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf PolicyMap) xs

PMFields : @0 List UInt8 → Set
PMFields xs = TLV Tag.OctetString  PMFieldsSeq xs

PolicyMapFieldsRep : @0 List UInt8 → Set
PolicyMapFieldsRep = &ₚ OID OID

RawPolicyMapFieldsRep : Raw PolicyMapFieldsRep
RawPolicyMapFieldsRep = Raw&ₚ RawOID RawOID

equivalentPolicyMapFields : Equivalent PolicyMapFieldsRep PolicyMapFields
proj₁ equivalentPolicyMapFields (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkPolicyMapFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalentPolicyMapFields (mkPolicyMapFields issuerDomainPolicy subjectDomainPolicy bs≡) = mk&ₚ issuerDomainPolicy subjectDomainPolicy bs≡

RawPolicyMapFields : Raw PolicyMapFields
RawPolicyMapFields =  Iso.raw equivalentPolicyMapFields RawPolicyMapFieldsRep

RawPMFields : Raw PMFields
RawPMFields = RawTLV _ (RawTLV _ (RawBoundedSequenceOf (RawTLV _ RawPolicyMapFields) 1))
