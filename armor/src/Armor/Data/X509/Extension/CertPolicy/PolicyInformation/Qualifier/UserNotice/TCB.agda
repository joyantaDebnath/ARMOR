open import Armor.Binary
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.NoticeReference.TCB
open import Armor.Data.X690-DER.SequenceOf.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X509.DisplayText.TCB
import      Armor.Grammar.Option
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq.TCB
open import Armor.Prelude

module Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.TCB where

open Armor.Grammar.Option UInt8
open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Seq.TCB UInt8

record UserNoticeFields (@0 bs : List UInt8) : Set where
  constructor mkUserNoticeFields
  field
    @0 {nr et} : List UInt8
    noticeRef : Option NoticeReference nr
    expText : Option DisplayText et
    @0 bs≡  : bs ≡ nr ++ et

UserNotice : (@0 _ : List UInt8) → Set
UserNotice xs = TLV Tag.Sequence UserNoticeFields xs

UserNoticeFieldsRep = &ₚ (Option NoticeReference) (Option DisplayText)

equivalentUserNoticeFields : Equivalent UserNoticeFieldsRep UserNoticeFields
proj₂ equivalentUserNoticeFields (mkUserNoticeFields noticeRef expText bs≡) = mk&ₚ noticeRef expText bs≡
proj₁ equivalentUserNoticeFields (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkUserNoticeFields fstₚ₁ sndₚ₁ bs≡

RawUserNoticeFieldsRep : Raw UserNoticeFieldsRep
RawUserNoticeFieldsRep = Raw&ₚ (RawOption RawNoticeReference) (RawOption RawDisplayText)

RawUserNoticeFields : Raw UserNoticeFields
RawUserNoticeFields = Iso.raw equivalentUserNoticeFields RawUserNoticeFieldsRep

RawUserNotice : Raw UserNotice
RawUserNotice = RawTLV _ RawUserNoticeFields
