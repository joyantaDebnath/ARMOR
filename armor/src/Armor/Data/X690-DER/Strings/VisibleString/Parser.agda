open import Armor.Binary
open import Armor.Data.X690-DER.Strings.VisibleString.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X690-DER.Strings.VisibleString.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.IList       UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

private
  here' = "X690-DER: Strings: VisibleString: "

  parseExact : ∀ n → Parser (Logging ∘ Dec) (ExactLength VisibleStringValue n)
  runParser (parseExact n) xs = do
    (yes (success pre₁ r₁ r₁≡ (mk×ₚ (mk×ₚ (singleton chars chars≡) (─ len₁)) range₁) suf₁ ps≡)) ←
      runParser
        (parseSigma'{B = λ xs₁ str → Erased (All (InRange 32 127) xs₁)}
          (Parallel.ExactLength.nosubstrings _)
          (λ {xs₁} x → erased? (All.all? (inRange? 32 127) _)) -- (λ {xs₁} x → All.all? (inRange? 32 127) _)
          (λ a₁ a₂ x → x) -- (λ a₁ a₂ x → x)
          (parseN n (tell $ here' String.++ "underflow")))
        xs
      where (no ¬p) → do
        tell $ here' String.++ "invalid character range: " String.++ show (map toℕ (take n xs))
        return ∘ no $ λ where
          (success prefix ._ refl (mk×ₚ (mkVisibleStringValue chars range refl) (─ refl)) suffix ps≡) → ‼
            contradiction (success chars _ refl (mk×ₚ (mk×ₚ self (─ refl)) (─ range)) _ ps≡) ¬p
    return (yes
      (success pre₁ _ r₁≡
        (mk×ₚ
          (mkVisibleStringValue chars (subst₀ (All (InRange 32 127)) (sym chars≡) (¡ range₁)) (sym chars≡))
          (─ len₁))
        _ ps≡))

parseVisibleString : Parser (Logging ∘ Dec) VisibleString
parseVisibleString = parseTLV _ here' _ parseExact
