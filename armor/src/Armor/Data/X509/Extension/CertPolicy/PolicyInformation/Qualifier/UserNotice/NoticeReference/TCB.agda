open import Armor.Binary
open import Armor.Data.X690-DER.SequenceOf.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X509.DisplayText.TCB
open import Armor.Data.X690-DER.Int.TCB
import Armor.Grammar.Definitions
import Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.NoticeReference.TCB where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Seq UInt8

record NoticeReferenceFields (@0 bs : List UInt8) : Set where
  constructor mkNoticeReferenceFields
  field
    @0 {org nn} : List UInt8
    organization : DisplayText org
    noticenums : IntegerSeq nn
    @0 bs≡  : bs ≡ org ++ nn

NoticeReferenceFieldsRep = (&ₚ DisplayText IntegerSeq)

equivalentNoticeReferenceFields : Equivalent NoticeReferenceFieldsRep NoticeReferenceFields
proj₁ equivalentNoticeReferenceFields (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkNoticeReferenceFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalentNoticeReferenceFields (mkNoticeReferenceFields organization noticenums bs≡) = mk&ₚ organization noticenums bs≡

RawNoticeReferenceFieldsRep : Raw NoticeReferenceFieldsRep
RawNoticeReferenceFieldsRep = Raw&ₚ RawDisplayText (RawTLV _ (RawSequenceOf RawInt))

NoticeReference : @0 List UInt8 → Set
NoticeReference xs = TLV Tag.Sequence NoticeReferenceFields xs

RawNoticeReference : Raw NoticeReference
RawNoticeReference = RawTLV _ (Iso.raw equivalentNoticeReferenceFields RawNoticeReferenceFieldsRep)
