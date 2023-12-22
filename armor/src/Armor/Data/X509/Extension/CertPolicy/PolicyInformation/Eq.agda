open import Armor.Binary
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Properties
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.SequenceOf
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.CertPolicy.PolicyInformation.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ PolicyInformationFields
  eq≋ = Iso.isoEq≋ iso (Seq.eq≋&ₚ it it)
    where
      instance
        e : Eq≋ (NonEmptySequenceOf PolicyQualifierInfo)
        e = SequenceOf.BoundedSequenceOfEq≋
