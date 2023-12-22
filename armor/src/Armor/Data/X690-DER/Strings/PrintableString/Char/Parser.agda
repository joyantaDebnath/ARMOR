open import Armor.Binary
open import Armor.Data.X690-DER.OctetString.TCB
open import Armor.Data.X690-DER.Strings.PrintableString.Char.Properties
open import Armor.Data.X690-DER.Strings.PrintableString.Char.TCB
open import Armor.Data.X690-DER.TLV.TCB
open import Armor.Data.X690-DER.Tag
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X690-DER.Strings.PrintableString.Char.Parser where

open Armor.Grammar.Parser UInt8

private
  here' = "X690-DER: Strings: PrintableString: Char: parseChar:"

parse : Parser (Logging ∘ Dec) PrintableStringChar
runParser parse [] = do
  tell $ here' String.++ " underflow"
  return ∘ no $ λ where
    (success prefix read read≡ value suffix ps≡) →
      contradiction{P = prefix ≡ []} (++-conicalˡ _ _ ps≡) (nonempty value)
runParser parse (x ∷ xs) =
  case printableStringChar? x of λ where
    (no ¬p) → do
      tell $ here' String.++ " invalid char: " String.++ (show ∘ toℕ $ x)
      return ∘ no $ λ where
        (success prefix read read≡ (mkPrintableStringChar c range refl) suffix ps≡) → ‼
            (case (‼ ps≡) of λ where
              refl → contradiction range ¬p)
    (yes p) →
      return (yes (success [ x ] _ refl (mkPrintableStringChar x p refl) _ refl))
