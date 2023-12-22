open import Armor.Binary
open import Armor.Data.Unicode
open import Armor.Data.X509.DirectoryString.Properties
open import Armor.Data.X509.DirectoryString.TCB
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.Strings
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Parallel
import      Armor.Grammar.Sum
open import Armor.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X509.DirectoryString.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.IList       UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Sum         UInt8

instance
  eq≋ : Eq≋ DirectoryString
  eq≋ =
    Iso.isoEq≋ iso
      (Sum.sumEq≋
        ⦃ Parallel.eq≋Σₚ it λ a → record { _≟_ = λ x y → yes (≤-irrelevant x y) } ⦄
        ⦃ Sum.sumEq≋
          ⦃ Parallel.eq≋Σₚ it λ a → record { _≟_ = λ x y → yes (≤-irrelevant x y) } ⦄
          ⦃ Sum.sumEq≋
            ⦃ Parallel.eq≋Σₚ it λ a → record { _≟_ = λ x y → yes (≤-irrelevant x y) } ⦄
            ⦃ Sum.sumEq≋ ⦃ Parallel.eq≋Σₚ it λ a → record { _≟_ = λ x y → yes (≤-irrelevant x y) } ⦄
                     ⦃ Parallel.eq≋Σₚ it λ a → record { _≟_ = λ x y → yes (≤-irrelevant x y) } ⦄ ⦄ ⦄ ⦄)
