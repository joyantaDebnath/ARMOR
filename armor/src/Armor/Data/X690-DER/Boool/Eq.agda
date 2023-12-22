open import Armor.Binary
open import Armor.Data.X690-DER.Boool.Properties
open import Armor.Data.X690-DER.Boool.TCB
import      Armor.Grammar.Definitions
open import Armor.Prelude

module Armor.Data.X690-DER.Boool.Eq where

open Armor.Grammar.Definitions UInt8

instance
  eq≋ : Eq≋ BoolValue
  Eq≋._≋?_ eq≋ (mkBoolValue true b trueᵣ refl) (mkBoolValue true b' trueᵣ refl) =
    yes ≋-refl
  Eq≋._≋?_ eq≋ (mkBoolValue true b vᵣ refl) (mkBoolValue false b' vᵣ' refl) =
    no λ where (mk≋ refl ())
  Eq≋._≋?_ eq≋ (mkBoolValue false b vᵣ refl) (mkBoolValue true b' vᵣ' refl) =
    no λ where (mk≋ refl ()) 
  Eq≋._≋?_ eq≋ (mkBoolValue false b falseᵣ refl) (mkBoolValue false b' falseᵣ refl) =
    yes ≋-refl
