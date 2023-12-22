open import Armor.Binary
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.Strings.PrintableString.Char.TCB
open import Armor.Data.X690-DER.TLV.TCB
open import Armor.Data.X690-DER.Tag
import      Armor.Grammar.Definitions
open import Armor.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Armor.Data.X690-DER.Strings.PrintableString.Char.Properties where

open Armor.Grammar.Definitions UInt8

@0 nonempty : NonEmpty PrintableStringChar
nonempty () refl

@0 nosubstrings : NoSubstrings PrintableStringChar
nosubstrings xs₁++ys₁≡xs₂++ys₂ (mkPrintableStringChar c range refl) (mkPrintableStringChar c₁ range₁ refl) =
  cong [_] (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂)

@0 unambiguousRange : ∀ {c} → Unique (PrintableStringCharRange c)
unambiguousRange space space = refl
unambiguousRange space (numbers (fst , _)) =
  contradiction{P = 48 ≤ 32} fst (toWitnessFalse{Q = 48 ≤? 32} tt)
unambiguousRange space (uppers (fst , _)) =
  contradiction{P = 65 ≤ 32} fst (toWitnessFalse{Q = 65 ≤? 32} tt)
unambiguousRange space (lowers (fst , snd)) =
  contradiction{P = 97 ≤ 32} fst (toWitnessFalse{Q = 97 ≤? 32} tt)
unambiguousRange apostrophe apostrophe = refl
unambiguousRange apostrophe (numbers (fst , _)) =
  contradiction{P = 48 ≤ 39} fst (toWitnessFalse{Q = 48 ≤? 39} tt)
unambiguousRange apostrophe (uppers (fst , snd)) =
  contradiction{P = 65 ≤ 39} fst (toWitnessFalse{Q = 65 ≤? 39} tt)
unambiguousRange apostrophe (lowers (fst , snd)) =
  contradiction{P = 97 ≤ 39} fst (toWitnessFalse{Q = 97 ≤? 39} tt)
unambiguousRange leftParen leftParen = refl
unambiguousRange leftParen (numbers (fst , snd)) =
  contradiction{P = 48 ≤ 40} fst (toWitnessFalse{Q = 48 ≤? 40} tt)
unambiguousRange leftParen (uppers (fst , snd)) =
  contradiction{P = 65 ≤ 40} fst (toWitnessFalse{Q = 65 ≤? 40} tt)
unambiguousRange leftParen (lowers (fst , snd)) =
  contradiction{P = 97 ≤ 40} fst (toWitnessFalse{Q = 97 ≤? 40} tt)
unambiguousRange rightParen rightParen = refl
unambiguousRange rightParen (numbers (fst , snd)) =
  contradiction{P = 48 ≤ 41} fst (toWitnessFalse{Q = 48 ≤? 41} tt)
unambiguousRange rightParen (uppers (fst , snd)) =
  contradiction{P = 65 ≤ 41} fst (toWitnessFalse{Q = 65 ≤? 41} tt)
unambiguousRange rightParen (lowers (fst , snd)) =
  contradiction{P = 97 ≤ 41} fst (toWitnessFalse{Q = 97 ≤? 41} tt)
unambiguousRange plus plus = refl
unambiguousRange plus (numbers (fst , _)) =
  contradiction{P = 48 ≤ 43} fst (toWitnessFalse{Q = 48 ≤? 43} tt)
unambiguousRange plus (uppers (fst , snd)) =
  contradiction{P = 65 ≤ 43} fst (toWitnessFalse{Q = 65 ≤? 43} tt)
unambiguousRange plus (lowers (fst , snd)) =
  contradiction{P = 97 ≤ 43} fst (toWitnessFalse{Q = 97 ≤? 43} tt)
unambiguousRange comma comma = refl
unambiguousRange comma (numbers (fst , snd)) =
  contradiction{P = 48 ≤ 44} fst (toWitnessFalse{Q = 48 ≤? 44} tt)
unambiguousRange comma (uppers (fst , snd)) =
  contradiction{P = 65 ≤ 44} fst (toWitnessFalse{Q = 65 ≤? 44} tt)
unambiguousRange comma (lowers (fst , snd)) =
  contradiction{P = 97 ≤ 44} fst (toWitnessFalse{Q = 97 ≤? 44} tt)
unambiguousRange hyphen hyphen = refl
unambiguousRange hyphen (numbers (fst , snd)) =
  contradiction{P = 48 ≤ 45} fst (toWitnessFalse{Q = 48 ≤? 45} tt)
unambiguousRange hyphen (uppers (fst , snd)) =
  contradiction{P = 65 ≤ 45} fst (toWitnessFalse{Q = 65 ≤? 45} tt)
unambiguousRange hyphen (lowers (fst , snd)) =
  contradiction{P = 97 ≤ 45} fst (toWitnessFalse{Q = 97 ≤? 45} tt)
unambiguousRange period period = refl
unambiguousRange period (numbers (fst , snd)) =
  contradiction{P = 48 ≤ 46} fst (toWitnessFalse{Q = 48 ≤? 46} tt)
unambiguousRange period (uppers (fst , snd)) =
  contradiction{P = 65 ≤ 46} fst (toWitnessFalse{Q = 65 ≤? 46} tt)
unambiguousRange period (lowers (fst , snd)) =
  contradiction{P = 97 ≤ 46} fst (toWitnessFalse{Q = 97 ≤? 46} tt)
unambiguousRange fslash fslash = refl
unambiguousRange fslash (numbers (fst , snd)) =
  contradiction{P = 48 ≤ 47} fst (toWitnessFalse{Q = 48 ≤? 47} tt)
unambiguousRange fslash (uppers (fst , snd)) =
  contradiction{P = 65 ≤ 47} fst (toWitnessFalse{Q = 65 ≤? 47} tt)
unambiguousRange fslash (lowers (fst , snd)) =
  contradiction{P = 97 ≤ 47} fst (toWitnessFalse{Q = 97 ≤? 47} tt)
unambiguousRange (numbers (fst , snd)) space =
  contradiction{P = 48 ≤ 32} fst (toWitnessFalse{Q = 48 ≤? 32} tt)
unambiguousRange (numbers (fst , snd)) apostrophe =
  contradiction{P = 48 ≤ 39} fst (toWitnessFalse{Q = 48 ≤? 39} tt)
unambiguousRange (numbers (fst , snd)) leftParen =
  contradiction{P = 48 ≤ 40} fst (toWitnessFalse{Q = 48 ≤? 40} tt)
unambiguousRange (numbers (fst , snd)) rightParen =
  contradiction{P = 48 ≤ 41} fst (toWitnessFalse{Q = 48 ≤? 41} tt)
unambiguousRange (numbers (fst , snd)) plus =
  contradiction{P = 48 ≤ 43} fst (toWitnessFalse{Q = 48 ≤? 43} tt)
unambiguousRange (numbers (fst , snd)) comma =
  contradiction{P = 48 ≤ 44} fst (toWitnessFalse{Q = 48 ≤? 44} tt)
unambiguousRange (numbers (fst , snd)) hyphen =
  contradiction{P = 48 ≤ 45} fst (toWitnessFalse{Q = 48 ≤? 45} tt)
unambiguousRange (numbers (fst , snd)) period =
  contradiction{P = 48 ≤ 46} fst (toWitnessFalse{Q = 48 ≤? 46} tt)
unambiguousRange (numbers (fst , snd)) fslash =
  contradiction{P = 48 ≤ 47} fst (toWitnessFalse{Q = 48 ≤? 47} tt)
unambiguousRange (numbers x₁@(_ , _)) (numbers x) =
  cong numbers (inRange-unique{A = ℕ}{B = UInt8} x₁ x)
unambiguousRange (numbers (fst , snd)) colon =
  contradiction{P = 58 ≤ 57} snd (toWitnessFalse{Q = 58 ≤? 57} tt)
unambiguousRange (numbers (fst , snd)) equals =
  contradiction{P = 61 ≤ 57} snd (toWitnessFalse{Q = 61 ≤? 57} tt)
unambiguousRange (numbers (fst , snd)) question =
  contradiction{P = 63 ≤ 57} snd (toWitnessFalse{Q = 63 ≤? 57} tt)
unambiguousRange (numbers (fst , snd)) (uppers (fst₁ , snd₁)) =
  contradiction{P = 65 ≤ 57} (≤-trans fst₁ snd) (toWitnessFalse{Q = 65 ≤? 57} tt)
unambiguousRange (numbers (fst , snd)) (lowers (fst₁ , snd₁)) =
  contradiction{P = 97 ≤ 57} (≤-trans fst₁ snd) (toWitnessFalse{Q = 97 ≤? 57} tt)
unambiguousRange colon (numbers (fst , snd)) =
  contradiction{P = 58 ≤ 57} snd (toWitnessFalse{Q = 58 ≤? 57} tt)
unambiguousRange colon colon = refl
unambiguousRange colon (uppers (fst , snd)) =
  contradiction{P = 65 ≤ 58} fst (toWitnessFalse{Q = 65 ≤? 58} tt)
unambiguousRange colon (lowers (fst , snd)) =
  contradiction{P = 97 ≤ 58} fst (toWitnessFalse{Q = 97 ≤? 58} tt)
unambiguousRange equals (numbers (fst , snd)) =
  contradiction{P = 61 ≤ 57} snd (toWitnessFalse{Q = 61 ≤? 57} tt)
unambiguousRange equals equals = refl
unambiguousRange equals (uppers (fst , snd)) =
  contradiction{P = 65 ≤ 61} fst (toWitnessFalse{Q = 65 ≤? 61} tt)
unambiguousRange equals (lowers (fst , snd)) =
  contradiction{P = 97 ≤ 61} fst (toWitnessFalse{Q = 97 ≤? 61} tt)
unambiguousRange question (numbers (fst , snd)) =
  contradiction{P = 63 ≤ 57} snd (toWitnessFalse{Q = 63 ≤? 57} tt)
unambiguousRange question question = refl
unambiguousRange question (uppers (fst , snd)) =
  contradiction{P = 65 ≤ 63} fst (toWitnessFalse{Q = 65 ≤? 63} tt)
unambiguousRange question (lowers (fst , snd)) =
  contradiction{P = 97 ≤ 63} fst (toWitnessFalse{Q = 97 ≤? 63} tt)
unambiguousRange (uppers (fst , snd)) space =
  contradiction{P = 65 ≤ 32} fst (toWitnessFalse{Q = 65 ≤? 32} tt)
unambiguousRange (uppers (fst , snd)) apostrophe =
  contradiction{P = 65 ≤ 39} fst (toWitnessFalse{Q = 65 ≤? 39} tt)
unambiguousRange (uppers (fst , snd)) leftParen =
  contradiction{P = 65 ≤ 40} fst (toWitnessFalse{Q = 65 ≤? 40} tt)
unambiguousRange (uppers (fst , snd)) rightParen =
  contradiction{P = 65 ≤ 41} fst (toWitnessFalse{Q = 65 ≤? 41} tt)
unambiguousRange (uppers (fst , snd)) plus =
  contradiction{P = 65 ≤ 43} fst (toWitnessFalse{Q = 65 ≤? 43} tt)
unambiguousRange (uppers (fst , snd)) comma =
  contradiction{P = 65 ≤ 44} fst (toWitnessFalse{Q = 65 ≤? 44} tt)
unambiguousRange (uppers (fst , snd)) hyphen =
  contradiction{P = 65 ≤ 45} fst (toWitnessFalse{Q = 65 ≤? 45} tt)
unambiguousRange (uppers (fst , snd)) period =
  contradiction{P = 65 ≤ 46} fst (toWitnessFalse{Q = 65 ≤? 46} tt)
unambiguousRange (uppers (fst , snd)) fslash =
  contradiction{P = 65 ≤ 47} fst (toWitnessFalse{Q = 65 ≤? 47} tt)
unambiguousRange (uppers (fst , snd)) (numbers (fst₁ , snd₁)) =
  contradiction{P = 65 ≤ 57} (≤-trans fst snd₁) (toWitnessFalse{Q = 65 ≤? 57} tt)
unambiguousRange (uppers (fst , snd)) colon =
  contradiction{P = 65 ≤ 58} fst (toWitnessFalse{Q = 65 ≤? 58} tt)
unambiguousRange (uppers (fst , snd)) equals =
  contradiction{P = 65 ≤ 61} fst (toWitnessFalse{Q = 65 ≤? 61} tt)
unambiguousRange (uppers (fst , snd)) question =
  contradiction{P = 65 ≤ 63} fst (toWitnessFalse{Q = 65 ≤? 63} tt)
unambiguousRange (uppers y@(fst , snd)) (uppers x) =
  cong uppers (inRange-unique{A = ℕ}{B = UInt8} y x)
unambiguousRange (uppers (fst , snd)) (lowers (fst₁ , snd₁)) =
  contradiction{P = 97 ≤ 90} (≤-trans fst₁ snd) (toWitnessFalse{Q = 97 ≤? 90} tt)
unambiguousRange (lowers (fst , snd)) space =
  contradiction{P = 97 ≤ 32} fst (toWitnessFalse{Q = 97 ≤? 32} tt)
unambiguousRange (lowers (fst , snd)) apostrophe =
  contradiction{P = 97 ≤ 39} fst (toWitnessFalse{Q = 97 ≤? 39} tt)
unambiguousRange (lowers (fst , snd)) leftParen =
  contradiction{P = 97 ≤ 40} fst (toWitnessFalse{Q = 97 ≤? 40} tt)
unambiguousRange (lowers (fst , snd)) rightParen =
  contradiction{P = 97 ≤ 41} fst (toWitnessFalse{Q = 97 ≤? 41} tt)
unambiguousRange (lowers (fst , snd)) plus =
  contradiction{P = 97 ≤ 43} fst (toWitnessFalse{Q = 97 ≤? 43} tt)
unambiguousRange (lowers (fst , snd)) comma =
  contradiction{P = 97 ≤ 44} fst (toWitnessFalse{Q = 97 ≤? 44} tt)
unambiguousRange (lowers (fst , snd)) hyphen =
  contradiction{P = 97 ≤ 45} fst (toWitnessFalse{Q = 97 ≤? 45} tt)
unambiguousRange (lowers (fst , snd)) period =
  contradiction{P = 97 ≤ 46} fst (toWitnessFalse{Q = 97 ≤? 46} tt)
unambiguousRange (lowers (fst , snd)) fslash =
  contradiction{P = 97 ≤ 47} fst (toWitnessFalse{Q = 97 ≤? 47} tt)
unambiguousRange (lowers (fst , snd)) (numbers (fst₁ , snd₁)) =
  contradiction (≤-trans fst snd₁) (toWitnessFalse{Q = 97 ≤? 57} tt)
unambiguousRange (lowers (fst , snd)) colon =
  contradiction{P = 97 ≤ 58} fst (toWitnessFalse{Q = 97 ≤? 58} tt)
unambiguousRange (lowers (fst , snd)) equals =
  contradiction{P = 97 ≤ 61} fst (toWitnessFalse{Q = 97 ≤? 61} tt)
unambiguousRange (lowers (fst , snd)) question =
  contradiction{P = 97 ≤ 63} fst (toWitnessFalse{Q = 97 ≤? 63} tt)
unambiguousRange (lowers (fst , snd)) (uppers (fst₁ , snd₁)) =
  contradiction (≤-trans fst snd₁) (toWitnessFalse{Q = _ ≤? _} tt)
unambiguousRange (lowers y@(fst , snd)) (lowers x) =
  cong lowers (inRange-unique{A = ℕ}{B = UInt8} y x)

@0 unambiguous : Unambiguous PrintableStringChar
unambiguous (mkPrintableStringChar c range refl) (mkPrintableStringChar .c range₁ refl) =
  case unambiguousRange range range₁ of λ where
    refl → refl

@0 nonmalleable : NonMalleable RawPrintableStringChar
nonmalleable (mkPrintableStringChar c range refl) (mkPrintableStringChar c₁ range₁ refl) refl =
  case (‼ unambiguousRange range range₁) of λ where
    refl → refl

printableStringChar? : Decidable (λ x → PrintableStringCharRange x)
printableStringChar? c =
  case
    (((c ≟ # 32 ⊎-dec c ≟ # 39) ⊎-dec (c ≟ # 40 ⊎-dec c ≟ # 41)) ⊎-dec ((c ≟ # 43 ⊎-dec c ≟ # 44) ⊎-dec (c ≟ # 45 ⊎-dec c ≟ # 46)))
    ⊎-dec ((c ≟ # 47 ⊎-dec inRange? 48 57 c) ⊎-dec (c ≟ # 58 ⊎-dec c ≟ # 61)) ⊎-dec ((c ≟ # 63 ⊎-dec inRange? 65 90 c) ⊎-dec inRange? 97 122 c)
  of λ where
    (no ¬p) → no λ where
      space → contradiction (inj₁ (inj₁ (inj₁ (inj₁ refl)))) ¬p
      apostrophe → contradiction (inj₁ (inj₁ (inj₁ (inj₂ refl)))) ¬p
      leftParen → contradiction (inj₁ (inj₁ (inj₂ (inj₁ refl)))) ¬p
      rightParen → contradiction (inj₁ (inj₁ (inj₂ (inj₂ refl)))) ¬p
      plus → contradiction (inj₁ (inj₂ (inj₁ (inj₁ refl)))) ¬p
      comma → contradiction (inj₁ (inj₂ (inj₁ (inj₂ refl)))) ¬p
      hyphen → contradiction (inj₁ (inj₂ (inj₂ (inj₁ refl)))) ¬p
      period → contradiction (inj₁ (inj₂ (inj₂ (inj₂ refl)))) ¬p
      fslash → contradiction (inj₂ (inj₁ (inj₁ (inj₁ refl)))) ¬p
      (numbers x) → contradiction (inj₂ (inj₁ (inj₁ (inj₂ x)))) ¬p
      colon → contradiction (inj₂ (inj₁ (inj₂ (inj₁ refl)))) ¬p
      equals → contradiction (inj₂ (inj₁ (inj₂ (inj₂ refl)))) ¬p
      question → contradiction (inj₂ (inj₂ (inj₁ (inj₁ refl)))) ¬p
      (uppers x) → contradiction (inj₂ (inj₂ (inj₁ (inj₂ x)))) ¬p
      (lowers x) → contradiction (inj₂ (inj₂ (inj₂ x))) ¬p
    (yes (inj₁ (inj₁ (inj₁ (inj₁ refl))))) → yes space
    (yes (inj₁ (inj₁ (inj₁ (inj₂ refl))))) → yes apostrophe
    (yes (inj₁ (inj₁ (inj₂ (inj₁ refl))))) → yes leftParen
    (yes (inj₁ (inj₁ (inj₂ (inj₂ refl))))) → yes rightParen
    (yes (inj₁ (inj₂ (inj₁ (inj₁ refl))))) → yes plus
    (yes (inj₁ (inj₂ (inj₁ (inj₂ refl))))) → yes comma
    (yes (inj₁ (inj₂ (inj₂ (inj₁ refl))))) → yes hyphen
    (yes (inj₁ (inj₂ (inj₂ (inj₂ refl))))) → yes period
    (yes (inj₂ (inj₁ (inj₁ (inj₁ refl))))) → yes fslash
    (yes (inj₂ (inj₁ (inj₁ (inj₂ y))))) → yes (numbers y)
    (yes (inj₂ (inj₁ (inj₂ (inj₁ refl))))) → yes colon
    (yes (inj₂ (inj₁ (inj₂ (inj₂ refl))))) → yes equals
    (yes (inj₂ (inj₂ (inj₁ (inj₁ refl))))) → yes question
    (yes (inj₂ (inj₂ (inj₁ (inj₂ y))))) → yes (uppers y)
    (yes (inj₂ (inj₂ (inj₂ y)))) → yes (lowers y)

instance
  PrintableStringCharEq≋ : Eq≋ PrintableStringChar
  Eq≋._≋?_ PrintableStringCharEq≋ (mkPrintableStringChar c₁ range₁ refl) (mkPrintableStringChar c₂ range₂ refl) =
    case c₁ ≟ c₂ of λ where
      (no ¬p) → no λ where ≋-refl → contradiction refl ¬p
      (yes refl) →
        case (‼ unambiguousRange range₁ range₂) ret (const _) of λ where
          refl → yes ≋-refl
