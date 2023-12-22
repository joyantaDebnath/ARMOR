open import Armor.Binary
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.NoticeReference
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.Properties
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.TCB
open import Armor.Data.X690-DER.SequenceOf.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X509.DisplayText
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ UserNoticeFields
  eq≋ = Iso.isoEq≋ iso (Seq.eq≋&ₚ it it)
