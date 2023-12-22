import Armor.Binary.Base64EncDec.Base64
import Armor.Binary.Base64EncDec.EncDec

module Armor.Binary.Base64EncDec where

open Armor.Binary.Base64EncDec.Base64 public
  hiding (charset ; ∈charsetUnique)

module Base64 where
  open Armor.Binary.Base64EncDec.Base64 public
    using (charset ; ∈charsetUnique)
  open Armor.Binary.Base64EncDec.EncDec public
