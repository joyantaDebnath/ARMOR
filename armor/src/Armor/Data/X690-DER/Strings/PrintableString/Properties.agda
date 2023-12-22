open import Armor.Binary
open import Armor.Data.X690-DER.Strings.PrintableString.Char
open import Armor.Data.X690-DER.Strings.PrintableString.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
open import Armor.Prelude

module Armor.Data.X690-DER.Strings.PrintableString.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.IList       UInt8

sizeUnique : ∀ {@0 bs} → (a₁ a₂ : IList PrintableStringChar bs) → size a₁ ≡ size a₂
sizeUnique nil nil = refl
sizeUnique nil (consIList (mkPrintableStringChar c₂ _ refl) t₂ ())
sizeUnique (consIList (mkPrintableStringChar c₁ _ refl) t₁ ()) nil
sizeUnique (consIList (mkPrintableStringChar c₁ _ refl) t₁ refl) (consIList (mkPrintableStringChar c₂ _ refl) t₂ refl) =
  cong suc (sizeUnique t₁ t₂)

@0 unambiguous : Unambiguous PrintableString
unambiguous = TLV.unambiguous (IList.unambiguous Char.unambiguous Char.nonempty Char.nosubstrings)

@0 nonmalleableValue : NonMalleable RawPrintableStringValue
nonmalleableValue snd snd₁ x =
  IList.nonmalleable Char.nonempty Char.nosubstrings Char.nonmalleable snd snd₁ x

instance
  PrintableStringEq≋ : Eq≋ (IList PrintableStringChar)
  PrintableStringEq≋ = IList.IListEq≋

@0 nonmalleable : NonMalleable RawPrintableString
nonmalleable = TLV.nonmalleable nonmalleableValue
