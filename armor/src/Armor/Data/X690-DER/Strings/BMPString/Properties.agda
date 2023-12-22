open import Armor.Binary
open import Armor.Data.X690-DER.Strings.BMPString.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.TLV.Properties as TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Data.Unicode.UTF16.Properties as UTF16
import      Armor.Grammar.Definitions.NonMalleable.Base
open import Armor.Prelude

module Armor.Data.X690-DER.Strings.BMPString.Properties where

open Armor.Grammar.Definitions.NonMalleable.Base UInt8

@0 nonmalleable : NonMalleable RawBMPString
nonmalleable = TLV.nonmalleable UTF16.nonmalleable
