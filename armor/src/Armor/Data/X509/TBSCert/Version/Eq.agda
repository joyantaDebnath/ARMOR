open import Armor.Binary
open import Armor.Data.X509.TBSCert.Version.TCB
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
open import Armor.Prelude

module Armor.Data.X509.TBSCert.Version.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8

instance
  eq≋ : Eq≋ Version
  eq≋ = Parallel.eq≋Σₚ
          it
          λ a → record { _≟_ = λ where
            a∈₁ a∈₂ → yes (erased-unique (∈-unique (toWitness{Q = unique? supportedVersions} tt)) a∈₁ a∈₂) }
