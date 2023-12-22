open import Armor.Binary
open import Armor.Data.Unicode.UTF32.Properties
open import Armor.Data.Unicode.UTF32.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.Unicode.UTF32.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.IList       UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

private
  here' = "Unicode: UTF32: "

parseChar : Parser (Logging ∘ Dec) UTF32Char
runParser parseChar xs = do
  (yes (success pre₁ ._ refl (mk×ₚ (mk×ₚ (singleton bs@(b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ []) refl) (─ refl)) (refl , u32₁)) suf₁ ps≡₁)) ←
    runParser
      (parseSigma'
        {B = λ where
          ._ (mk×ₚ (singleton (b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ []) refl) (─ refl)) →
            b₁ ≡ # 0 × UTF32CharRange b₂ b₃ b₄}
        (Parallel.ExactLength.nosubstrings _)
        (λ where
          {._} (mk×ₚ (singleton (b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ []) refl) (─ refl)) →
            _ ≟ (# 0) ×-dec utf32CharRange? _ _ _)
        (λ where
          (mk×ₚ (singleton (b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ []) refl) (─ refl)) (mk×ₚ (singleton ._ refl) (─ refl)) x → x)
        (parseN 4 (tell $ here' String.++ "parseChar: underflow")))
      xs
    where no ¬p → do
      tell $ here' String.++ "parseChar: underflow or invalid range: " String.++ show (map toℕ (take 4 xs))
      return ∘ no $ λ where
        (success prefix@.(# 0 ∷ b₂ ∷ b₃ ∷ [ b₄ ]) read read≡ (mkUTF32Char b₂ b₃ b₄ range refl) suffix refl) → ‼
          contradiction
            (success prefix _ refl (mk×ₚ (mk×ₚ (singleton prefix refl) (─ refl)) (refl , range)) _ refl)
            ¬p
  return (yes (success pre₁ _ refl (mkUTF32Char b₂ b₃ b₄ u32₁ refl) suf₁ ps≡₁))

parse : ∀ n → Parser (Logging ∘ Dec) (ExactLength UTF32 n)
parse = parseIList (tell $ here' String.++ "parse: underflow") _ Char.nonempty Char.nosubstrings parseChar
