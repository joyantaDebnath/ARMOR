open import Armor.Binary
open import Armor.Data.X509.GeneralNames.GeneralName.Properties
open import Armor.Data.X509.GeneralNames.GeneralName.TCB
open import Armor.Data.X509.Name
open import Armor.Data.X690-DER
import      Armor.Grammar.Definitions
import      Armor.Grammar.Sum
open import Armor.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Armor.Data.X509.GeneralNames.GeneralName.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Sum         UInt8

instance
  eq≋ : Eq≋ GeneralName
  eq≋ =
    Iso.isoEq≋ iso
      (Sum.sumEq≋ ⦃ eq₂ =
       Sum.sumEq≋ ⦃ eq₂ =
       Sum.sumEq≋ ⦃ eq₂ =
       Sum.sumEq≋ ⦃ eq₂ =
       Sum.sumEq≋ ⦃ eq₂ =
       Sum.sumEq≋ ⦃ eq₂ =
       Sum.sumEq≋ ⦃ eq₂ = Sum.sumEq≋ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄)
       
