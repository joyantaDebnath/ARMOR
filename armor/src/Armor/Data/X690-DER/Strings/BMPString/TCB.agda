open import Armor.Binary
open import Armor.Data.Unicode.UTF16.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.IList.TCB
import      Armor.Grammar.Sum.TCB
open import Armor.Prelude

module Armor.Data.X690-DER.Strings.BMPString.TCB where

open Armor.Grammar.IList.TCB UInt8
open Armor.Grammar.Definitions.NonMalleable UInt8

BMPString : @0 List UInt8 → Set
BMPString xs = TLV Tag.BMPString BMP xs

RawBMPString : Raw BMPString 
RawBMPString = RawTLV _ RawBMP
