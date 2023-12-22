open import Armor.Binary
open import Armor.Data.X509.Extension.CertPolicy.PolicyInformation
open import Armor.Data.X509.Extension.CertPolicy.TCB
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.SequenceOf
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.CertPolicy.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

@0 unambiguous : Unambiguous CertPolFields
unambiguous = TLV.unambiguous (TLV.unambiguous
  (SequenceOf.Bounded.unambiguous PolicyInformation.unambiguous TLV.nonempty TLV.nosubstrings))

@0 nonmalleable : NonMalleable RawCertPolFields
nonmalleable = TLV.nonmalleable (TLV.nonmalleable
  (SequenceOf.Bounded.nonmalleable TLV.nonempty TLV.nosubstrings PolicyInformation.nonmalleable))
