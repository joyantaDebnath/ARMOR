open import Armor.Binary
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X509.SignAlg.RSA.PSS
open import Armor.Data.X509.SignAlg.RSA.TCB
open import Armor.Data.X509.HashAlg
import      Armor.Grammar.Definitions
import      Armor.Grammar.Sum
open import Armor.Prelude

module Armor.Data.X509.SignAlg.RSA.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Sum         UInt8

-- instance
--   eq≋Supported : Eq≋ Supported
--   eq≋Supported =
--     Sum.sumEq≋ ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₂ =
--     Sum.sumEq≋ ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₂ = Sum.sumEq≋ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄
