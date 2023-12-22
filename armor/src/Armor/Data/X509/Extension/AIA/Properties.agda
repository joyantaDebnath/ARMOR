open import Armor.Binary
open import Armor.Data.X509.Extension.AIA.TCB
open import Armor.Data.X509.Extension.AIA.AccessDesc
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Prelude

module Armor.Data.X509.Extension.AIA.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8

@0 unambiguous : Unambiguous AIAFields
unambiguous = TLV.unambiguous (TLV.unambiguous (SequenceOf.Bounded.unambiguous
  AccessDesc.unambiguous TLV.nonempty TLV.nosubstrings))

@0 nonmalleable : NonMalleable RawAIAFields
nonmalleable = TLV.nonmalleable (TLV.nonmalleable (SequenceOf.Bounded.nonmalleable
  TLV.nonempty TLV.nosubstrings AccessDesc.nonmalleable))
