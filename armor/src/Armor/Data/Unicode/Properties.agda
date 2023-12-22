open import Armor.Binary
open import Armor.Data.Unicode.UTF8
open import Armor.Data.Unicode.UTF16
open import Armor.Data.Unicode.UTF32
open import Armor.Data.Unicode.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
open import Armor.Prelude

module Armor.Data.Unicode.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.IList       UInt8

instance
  Eq≋Unicode : Eq≋ Unicode
  Eq≋._≋?_ Eq≋Unicode (utf8 x) (utf8 x₁) =
    case x ≋? x₁ of λ where
      (no ¬p) → no λ where ≋-refl → contradiction ≋-refl ¬p
      (yes ≋-refl) → yes ≋-refl
  Eq≋._≋?_ Eq≋Unicode (utf8 x) (utf16 x₁) = no λ where (mk≋ refl ())
  Eq≋._≋?_ Eq≋Unicode (utf8 x) (utf32 x₁) = no λ where (mk≋ refl ())
  Eq≋._≋?_ Eq≋Unicode (utf16 x) (utf8 x₁) = no λ where (mk≋ refl ())
  Eq≋._≋?_ Eq≋Unicode (utf16 x) (utf16 x₁) =
    case x ≋? x₁ of λ where
      (no ¬p) → no λ where ≋-refl → contradiction ≋-refl ¬p
      (yes ≋-refl) → yes ≋-refl
  Eq≋._≋?_ Eq≋Unicode (utf16 x) (utf32 x₁) = no λ where (mk≋ refl ())
  Eq≋._≋?_ Eq≋Unicode (utf32 x) (utf8 x₁) = no λ where (mk≋ refl ())
  Eq≋._≋?_ Eq≋Unicode (utf32 x) (utf16 x₁) = no λ where (mk≋ refl ())
  Eq≋._≋?_ Eq≋Unicode (utf32 x) (utf32 x₁) =
    case x ≋? x₁ of λ where
      (no ¬p) → no λ where ≋-refl → contradiction ≋-refl ¬p
      (yes ≋-refl) → yes ≋-refl
