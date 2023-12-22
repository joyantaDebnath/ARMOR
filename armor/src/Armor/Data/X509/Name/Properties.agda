open import Armor.Binary
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Data.X509.Name.RDN.Properties as RDN
open import Armor.Data.X509.Name.RDN.TCB
open import Armor.Data.X509.Name.TCB
import      Armor.Grammar.Definitions
open import Armor.Prelude

module Armor.Data.X509.Name.Properties where

open Armor.Grammar.Definitions UInt8

@0 unambiguous : Unambiguous Name
unambiguous = TLV.unambiguous (SequenceOf.unambiguous RDN.unambiguous TLV.nonempty TLV.nosubstrings)

@0 nonmalleable : NonMalleable RawName
nonmalleable = TLV.nonmalleable {R = RawSequenceOf RawRDN} (SequenceOf.nonmalleable {R = RawRDN} TLV.nonempty TLV.nosubstrings RDN.nonmalleable)
