open import Armor.Binary
import      Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.TCB.OIDs as OIDs
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.Sequence.DefinedByOID
open import Armor.Data.X690-DER.SequenceOf.TCB
open import Armor.Data.X690-DER.Strings.IA5String.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Sum.TCB
open import Armor.Prelude

module Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.TCB where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Sum.TCB     UInt8

CPSURIQualifierParam : ∀ {@0 bs} → OID bs → @0 List UInt8 → Set
CPSURIQualifierParam o =
     IA5String
  ×ₚ (λ _ → (_≋_{A = OIDValue} (TLV.val o) OIDs.CPSURI))

CPSURIQualifier = DefinedByOIDFields CPSURIQualifierParam

RawCPSURIQualifierParam : Raw₁ RawOID CPSURIQualifierParam
Raw₁.D RawCPSURIQualifierParam _ = Raw.D RawIA5String
Raw₁.to RawCPSURIQualifierParam _ cps = Raw.to RawIA5String (fstₚ cps)

UserNoticeQualifierParam : ∀ {@0 bs} → OID bs → @0 List UInt8 → Set
UserNoticeQualifierParam o =
     UserNotice
  ×ₚ λ _ → (_≋_{A = OIDValue} (TLV.val o) OIDs.UserNotice)

UserNoticeQualifier = DefinedByOIDFields UserNoticeQualifierParam

RawUserNoticeQualifierParam : Raw₁ RawOID UserNoticeQualifierParam
Raw₁.D RawUserNoticeQualifierParam o = Raw.D RawUserNotice
Raw₁.to RawUserNoticeQualifierParam o unq = Raw.to RawUserNotice (fstₚ unq)

data PolicyQualifierInfoFields : @0 List UInt8 → Set where
  cpsURI : ∀ {@0 bs} → CPSURIQualifier bs → PolicyQualifierInfoFields bs
  userNotice : ∀ {@0 bs} → UserNoticeQualifier bs → PolicyQualifierInfoFields bs

PolicyQualifierInfo : @0 List UInt8 → Set
PolicyQualifierInfo xs = TLV Tag.Sequence PolicyQualifierInfoFields xs

PolicyQualifiersSeq : @0 List UInt8 → Set
PolicyQualifiersSeq xs = TLV Tag.Sequence (NonEmptySequenceOf PolicyQualifierInfo) xs

RawUserNoticeQualifier : Raw UserNoticeQualifier
RawUserNoticeQualifier = RawDefinedByOIDFields RawUserNoticeQualifierParam

RawCPSURIQualifier : Raw CPSURIQualifier
RawCPSURIQualifier = RawDefinedByOIDFields RawCPSURIQualifierParam

PolicyQualifierInfoFieldsRep = Sum CPSURIQualifier UserNoticeQualifier

equivalentPolicyQualifierInfoFields : Equivalent PolicyQualifierInfoFieldsRep PolicyQualifierInfoFields
proj₁ equivalentPolicyQualifierInfoFields (Armor.Grammar.Sum.TCB.inj₁ x) = cpsURI x
proj₁ equivalentPolicyQualifierInfoFields (Armor.Grammar.Sum.TCB.inj₂ x) = userNotice x
proj₂ equivalentPolicyQualifierInfoFields (cpsURI x) = inj₁ x
proj₂ equivalentPolicyQualifierInfoFields (userNotice x) = inj₂ x

RawPolicyQualifierInfoFieldsRep : Raw PolicyQualifierInfoFieldsRep
RawPolicyQualifierInfoFieldsRep = RawSum RawCPSURIQualifier RawUserNoticeQualifier

RawPolicyQualifiersSeq : Raw PolicyQualifiersSeq
RawPolicyQualifiersSeq = RawTLV _ (RawBoundedSequenceOf (RawTLV _ (Iso.raw equivalentPolicyQualifierInfoFields RawPolicyQualifierInfoFieldsRep)) 1)
