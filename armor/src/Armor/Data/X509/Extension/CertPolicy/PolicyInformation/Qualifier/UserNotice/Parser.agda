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
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Seq
import      Armor.Grammar.Sum
open import Armor.Prelude

module Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Seq         UInt8
open Armor.Grammar.Sum         UInt8

private
  here' = "X509: Extension: CertPolicy: PlicyInformation: Qualifier: UserNotice"

parseUserNoticeFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength UserNoticeFields n)
parseUserNoticeFields n =
  parseEquivalent (Parallel.equivalent₁ equivalentUserNoticeFields)
    (parseOption₂ here' TLV.nosubstrings DisplayText.nosubstrings
      (DisplayText.noconfusionTLV (toWitnessFalse{Q = _ ∈? _} tt))
      parseNoticeReference parseDisplayText
      n)

parseUserNotice : Parser (Logging ∘ Dec) UserNotice
parseUserNotice =
  parseTLV _ here' _ parseUserNoticeFields
