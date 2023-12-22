open import Armor.Binary
open import Armor.Data.Unicode.UTF32.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
open import Armor.Prelude
  hiding (module Char)

module Armor.Data.Unicode.UTF32.Properties where

open Armor.Grammar.Definitions      UInt8
open Armor.Grammar.IList            UInt8

utf32CharRange? : ∀ b₂ b₃ b₄ → Dec (UTF32CharRange b₂ b₃ b₄)
utf32CharRange? b₂ b₃ b₄
  with b₂ ≟ # 0
... | no b₂≢0
  with inRange? 1 2 b₂
... | yes p = yes (00010000-0010ffff p)
... | no ¬p = no λ where
  (00000000-0000d7ff x) → contradiction refl b₂≢0
  (0000e000-0000ffff x) → contradiction refl b₂≢0
  (00010000-0010ffff x) → contradiction x ¬p
utf32CharRange? ._ b₃ b₄ | yes refl =
  case toℕ b₃ ≤? 215 of λ where
    (yes b₃≤215) → yes (00000000-0000d7ff b₃≤215)
    (no b₃≰215) →
      case toℕ b₃ ≥? 224 of λ where
        (yes b₃≥224) → yes (0000e000-0000ffff b₃≥224)
        (no b₃≱224) → no λ where
          (00000000-0000d7ff x) → contradiction x b₃≰215
          (0000e000-0000ffff x) → contradiction x b₃≱224

module Char where
  open import Data.Nat.Properties
    hiding (_≟_)

  rangeUnique : ∀ {b₂ b₃ b₄} → Unique (UTF32CharRange b₂ b₃ b₄)
  rangeUnique (00000000-0000d7ff x) (00000000-0000d7ff x₁) = cong 00000000-0000d7ff (≤-unique x x₁)
  rangeUnique (00000000-0000d7ff x) (0000e000-0000ffff x₁) =
    contradiction{P = 224 ≤ 215} (≤-trans x₁ x) (toWitnessFalse{Q = 224 ≤? 215} tt)
  rangeUnique (0000e000-0000ffff x) (00000000-0000d7ff x₁) =
    contradiction{P = 224 ≤ 215} (≤-trans x x₁) (toWitnessFalse{Q = 224 ≤? 215} tt)
  rangeUnique (0000e000-0000ffff x) (0000e000-0000ffff x₁) =
    cong 0000e000-0000ffff (≤-unique x x₁)
  rangeUnique (00010000-0010ffff x) (00010000-0010ffff x₁) =
    cong 00010000-0010ffff (inRange-unique{A = ℕ}{B = UInt8} x x₁)

  @0 nonempty : NonEmpty UTF32Char
  nonempty (mkUTF32Char b₂ b₃ b₄ range refl) ()

  @0 nosubstrings : NoSubstrings UTF32Char
  nosubstrings refl (mkUTF32Char b₂ b₃ b₄ range refl) (mkUTF32Char b₅ b₆ b₇ range₁ refl) = refl

  @0 unambiguous : Unambiguous UTF32Char
  unambiguous (mkUTF32Char b₂ b₃ b₄ range refl) (mkUTF32Char .b₂ .b₃ .b₄ range₁ refl) =
    case (‼ rangeUnique range range₁) of λ where
      refl → refl

  @0 nonmalleable : NonMalleable RawUTF32Char
  nonmalleable (mkUTF32Char b₂ b₃ b₄ range refl) (mkUTF32Char b₅ b₆ b₇ range₁ refl) refl =
    case rangeUnique range range₁ of λ where
      refl → refl

  instance
    UTF32CharEq≋ : Eq≋ UTF32Char
    Eq≋._≋?_ UTF32CharEq≋ (mkUTF32Char b₁₂ b₁₃ b₁₄ range₁ refl) (mkUTF32Char b₂₂ b₂₃ b₂₄ range₂ refl) =
      case b₁₂ ∷ b₁₃ ∷ [ b₁₄ ] ≟ b₂₂ ∷ b₂₃ ∷ [ b₂₄ ] of λ where
        (no ¬p) → no λ where
          ≋-refl → contradiction refl ¬p
        (yes refl) →
          case ‼ rangeUnique range₁ range₂ ret (const _) of λ where
            refl → yes ≋-refl

@0 unambiguous : Unambiguous UTF32
unambiguous = IList.unambiguous Char.unambiguous Char.nonempty Char.nosubstrings

@0 nonmalleable : NonMalleable RawUTF32
nonmalleable = IList.nonmalleable Char.nonempty Char.nosubstrings Char.nonmalleable
  
instance
  UTF32Eq≋ : Eq≋ UTF32
  UTF32Eq≋ = IList.IListEq≋
