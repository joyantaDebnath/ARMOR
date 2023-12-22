open import Armor.Binary
open import Armor.Data.X509.Extension.EKU.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.SequenceOf

open import Armor.Prelude

module Armor.Data.X509.Extension.EKU.Properties where

open Armor.Grammar.Definitions UInt8

@0 unambiguous : Unambiguous EKUFields
unambiguous = TLV.unambiguous (TLV.unambiguous
                         (SequenceOf.Bounded.unambiguous OID.unambiguous  TLV.nonempty TLV.nosubstrings))

@0 nonmalleable : NonMalleable RawEKUFields
nonmalleable = TLV.nonmalleable (TLV.nonmalleable
                        (SequenceOf.Bounded.nonmalleable TLV.nonempty TLV.nosubstrings  OID.nonmalleable))
