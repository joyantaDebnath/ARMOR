open import Armor.Binary
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.NoticeReference
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.TCB
open import Armor.Data.X690-DER.SequenceOf.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X509.DisplayText
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
import      Armor.Grammar.Sum
open import Armor.Prelude

module Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8
open Armor.Grammar.Sum         UInt8

iso : Iso UserNoticeFieldsRep UserNoticeFields
proj₁ iso = equivalentUserNoticeFields
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkUserNoticeFields noticeRef expText bs≡) = refl

private
  @0 nc : NoConfusion NoticeReference DisplayText
  nc = symNoConfusion{A = DisplayText}{B = NoticeReference}
         (NoConfusion.equivalent{A₁ = Sum _ _}{A₂ = DisplayText}{NoticeReference}
           DisplayText.equivalent
           (symNoConfusion{NoticeReference}{Sum _ _}
             (Sum.noconfusion{NoticeReference}
               (NoConfusion.sigmaₚ₁ᵣ{A₁ = NoticeReference}
                 (TLV.noconfusion λ ()))
               (Sum.noconfusion{NoticeReference}
                 (NoConfusion.sigmaₚ₁ᵣ{A₁ = NoticeReference} (TLV.noconfusion λ ()))
                 (Sum.noconfusion{NoticeReference}
                   (NoConfusion.sigmaₚ₁ᵣ{A₁ = NoticeReference} (TLV.noconfusion λ ()))
                   (NoConfusion.sigmaₚ₁ᵣ{A₁ = NoticeReference} (TLV.noconfusion λ ())))))))

@0 unambiguous : Unambiguous UserNotice
unambiguous =
  TLV.unambiguous
    (Iso.unambiguous iso
      (Seq.unambiguousOption₂
        NoticeReference.unambiguous TLV.nosubstrings TLV.nonempty
        DisplayText.unambiguous DisplayText.nonempty
        nc))

@0 nonmalleable : NonMalleable RawUserNotice
nonmalleable = TLV.nonmalleable
                 (Iso.nonmalleable iso RawUserNoticeFieldsRep
                   (Seq.nonmalleable (Option.nonmalleable _ NoticeReference.nonmalleable)
                     (Option.nonmalleable _ DisplayText.nonmalleable)))
