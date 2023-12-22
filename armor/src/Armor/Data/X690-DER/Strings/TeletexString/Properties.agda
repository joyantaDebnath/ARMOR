open import Armor.Binary
open import Armor.Data.X690-DER.Strings.TeletexString.TCB
import      Armor.Data.X690-DER.TLV.Properties as TLV
import      Armor.Grammar.Definitions.NonMalleable.Base
import      Armor.Data.X690-DER.OctetString.Properties as OctetString
open import Armor.Prelude

module Armor.Data.X690-DER.Strings.TeletexString.Properties where

open Armor.Grammar.Definitions.NonMalleable.Base UInt8

@0 nonmalleable : NonMalleable RawTeletexString
nonmalleable = TLV.nonmalleable OctetString.nonmalleableValue
