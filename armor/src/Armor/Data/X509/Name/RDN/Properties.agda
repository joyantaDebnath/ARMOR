open import Armor.Binary
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.SetOf
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X509.Name.RDN.ATV
open import Armor.Data.X509.Name.RDN.TCB
import      Armor.Grammar.Definitions
open import Armor.Prelude

module Armor.Data.X509.Name.RDN.Properties where

open Armor.Grammar.Definitions UInt8

module RDN where
  @0 [_]unambiguous : ∀ t → Unambiguous [ t ]RDN
  [ t ]unambiguous = TLV.unambiguous (SetOf.unambiguousFields ATV.unambiguous TLV.nonempty TLV.nosubstrings)

  @0 unambiguous : Unambiguous RDN
  unambiguous = [ Tag.Sett ]unambiguous

  @0 [_]nonmalleable : ∀ t → NonMalleable [ t ]RawRDN
  [ t ]nonmalleable = TLV.nonmalleable (SetOf.nonmalleableFields {R = RawATV} TLV.nonempty TLV.nosubstrings ATV.nonmalleable)

  @0 nonmalleable : NonMalleable RawRDN
  nonmalleable = SetOf.nonmalleable{R = RawATV} TLV.nonempty TLV.nosubstrings ATV.nonmalleable

module Sequence where
  @0 unambiguous : Unambiguous RDNSequence
  unambiguous = TLV.unambiguous (SequenceOf.unambiguous RDN.unambiguous TLV.nonempty TLV.nosubstrings)

  @0 nonmalleable : NonMalleable RawRDNSequence
  nonmalleable = TLV.nonmalleable {R = RawSequenceOf RawRDN} (SequenceOf.nonmalleable {R = RawRDN} TLV.nonempty TLV.nosubstrings RDN.nonmalleable)

open RDN public

