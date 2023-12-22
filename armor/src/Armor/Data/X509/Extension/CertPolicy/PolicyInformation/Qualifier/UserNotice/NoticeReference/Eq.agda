open import Armor.Binary
open import Armor.Data.X509.DisplayText
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.NoticeReference.Properties
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.NoticeReference.TCB
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.SequenceOf
import      Armor.Grammar.Definitions
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.NoticeReference.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8
          
instance
  NoticeReferenceEq : Eq (Exists─ _ NoticeReferenceFields)
  NoticeReferenceEq =
    Iso.isoEq iso (Seq.eq&ₚ it it)
  
  eq≋ : Eq≋ NoticeReferenceFields
  eq≋ = Eq⇒Eq≋ it
