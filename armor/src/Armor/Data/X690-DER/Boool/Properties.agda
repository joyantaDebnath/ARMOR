open import Armor.Binary
open import Armor.Data.X690-DER.Boool.TCB
import      Armor.Data.X690-DER.TLV.Properties as TLV
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Grammar.Definitions
open import Armor.Prelude

module Armor.Data.X690-DER.Boool.Properties where

open Armor.Grammar.Definitions              UInt8

nonempty : NonEmpty BoolValue
nonempty () refl

@0 nosubstrings : NoSubstrings BoolValue
nosubstrings x (mkBoolValue v b vᵣ bs≡) (mkBoolValue v₁ b₁ vᵣ₁ bs≡₁) =
  proj₁ $ Lemmas.length-++-≡ _ _ _ _ x (trans (cong length bs≡) (cong length (sym bs≡₁)))

@0 unambiguousValue : Unambiguous BoolValue
unambiguousValue (mkBoolValue .#0 .(# 0) falseᵣ refl) (mkBoolValue .#0 .(# 0) falseᵣ refl) = refl
unambiguousValue (mkBoolValue .#0 .(# 0) falseᵣ refl) (mkBoolValue .#1 .(# 255) trueᵣ ())
unambiguousValue (mkBoolValue .#1 .(# 255) trueᵣ refl) (mkBoolValue .#0 .(# 0) falseᵣ ())
unambiguousValue (mkBoolValue .#1 .(# 255) trueᵣ refl) (mkBoolValue .#1 .(# 255) trueᵣ refl) = refl

@0 unambiguous : Unambiguous Boool
unambiguous = TLV.unambiguous unambiguousValue

@0 nonmalleableValue : NonMalleable RawBoolValue
nonmalleableValue (mkBoolValue #0 ._ falseᵣ refl) (mkBoolValue #0 ._ falseᵣ refl) _ = refl
nonmalleableValue (mkBoolValue #1 ._ trueᵣ refl)  (mkBoolValue #1 ._ trueᵣ refl) _ = refl

@0 nonmalleable : NonMalleable RawBoool
nonmalleable = TLV.nonmalleable nonmalleableValue
