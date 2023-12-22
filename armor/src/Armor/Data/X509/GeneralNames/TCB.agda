open import Armor.Binary
open import Armor.Data.X509.Name.TCB
open import Armor.Data.X509.GeneralNames.GeneralName.TCB
open import Armor.Data.X690-DER.OID.TCB
open import Armor.Data.X690-DER.OctetString.TCB
open import Armor.Data.X690-DER.Strings
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.SequenceOf.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel.TCB
import      Armor.Grammar.Sum.TCB
open import Armor.Prelude

module Armor.Data.X509.GeneralNames.TCB where

open      Armor.Grammar.Definitions              UInt8
open      Armor.Grammar.Parallel.TCB             UInt8
open      Armor.Grammar.Sum.TCB                  UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.6
--    GeneralNames ::= SEQUENCE SIZE (1..MAX) OF GeneralName

GeneralNamesElems = NonEmptySequenceOf GeneralName
GeneralNames = TLV Tag.Sequence GeneralNamesElems

RawGeneralNamesElems : Raw GeneralNamesElems
RawGeneralNamesElems = RawBoundedSequenceOf RawGeneralName 1

RawGeneralNames : Raw GeneralNames
RawGeneralNames = RawTLV _ RawGeneralNamesElems
