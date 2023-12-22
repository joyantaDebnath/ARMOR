open import Armor.Binary
import      Armor.Data.X509.Extension.AIA.AccessDesc.TCB.OIDs as OIDs
open import Armor.Data.X509.Extension.AIA.AccessDesc.TCB
open import Armor.Data.X509.GeneralNames
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.Sequence.DefinedByOID
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
open import Armor.Prelude

module Armor.Data.X509.Extension.AIA.AccessDesc.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8

instance
  eq≋ : Eq≋ (DefinedByOIDFields AccessDescParam)
  eq≋ =
    DefinedByOID.eq≋ _
      λ o → Parallel.eq≋Σₚ it λ _ →
        record
          { _≟_ = λ x y → yes (T-unique x y)
          }
