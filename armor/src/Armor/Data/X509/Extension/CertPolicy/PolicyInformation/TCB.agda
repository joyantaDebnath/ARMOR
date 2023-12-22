open import Armor.Binary
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Seq.TCB
open import Armor.Prelude

module Armor.Data.X509.Extension.CertPolicy.PolicyInformation.TCB where

open Armor.Grammar.Definitions              UInt8
open Armor.Grammar.Option UInt8
open Armor.Grammar.Seq.TCB UInt8

record PolicyInformationFields (@0 bs : List UInt8) : Set where
  constructor mkPolicyInformationFields
  field
    @0 {pid pqls} : List UInt8
    cpid : OID pid
    cpqls : Option PolicyQualifiersSeq pqls
    @0 bs≡  : bs ≡ pid ++ pqls

PolicyInformation : @0 List UInt8 → Set
PolicyInformation xs = TLV Tag.Sequence PolicyInformationFields xs

PolicyInformationFieldsRep = &ₚ OID (Option PolicyQualifiersSeq)

equivalentPolicyInformationFields : Equivalent PolicyInformationFieldsRep PolicyInformationFields
proj₂ equivalentPolicyInformationFields (mkPolicyInformationFields cpid cpqls bs≡) = Armor.Grammar.Seq.TCB.mk&ₚ cpid cpqls bs≡
proj₁ equivalentPolicyInformationFields (Armor.Grammar.Seq.TCB.mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkPolicyInformationFields  fstₚ₁ sndₚ₁ bs≡

RawPolicyInformationFieldsRep : Raw PolicyInformationFieldsRep
RawPolicyInformationFieldsRep = Raw&ₚ RawOID (RawOption RawPolicyQualifiersSeq)

RawPolicyInformationFields : Raw PolicyInformationFields
RawPolicyInformationFields = Iso.raw equivalentPolicyInformationFields RawPolicyInformationFieldsRep

RawPolicyInformation : Raw PolicyInformation
RawPolicyInformation = RawTLV _ RawPolicyInformationFields
