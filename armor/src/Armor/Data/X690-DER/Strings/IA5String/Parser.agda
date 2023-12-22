open import Armor.Binary
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.Strings.IA5String.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X690-DER.Strings.IA5String.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

parseIA5StringValue : ∀ n → Parser (Logging ∘ Dec) (ExactLength IA5StringValue n)
runParser (parseIA5StringValue n) xs = do
  yes (success pre₀ r₀ r₀≡ (mk×ₚ (singleton os₀ refl) (─ osLen)) suf₀ ps≡₀) ← runParser (OctetString.parseValue n) xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk×ₚ (mkIA5StringValue str all<128) strLen) suffix ps≡) →
          contradiction
            (success prefix _ read≡
              (mk×ₚ str strLen) _ ps≡)
            ¬parse
  case All.all? (Fin._<? (# 128)) os₀ of λ where
    (no  all≮128) → do
      tell $ here' String.++ ": value violation"
      return ∘ no $ λ where
        (success .str' _ read≡ (mk×ₚ (mkIA5StringValue (singleton str' refl) all<128) (─ strLen)) suffix ps≡) → ‼
          let @0 pre₀≡ : pre₀ ≡ str'
              pre₀≡ = proj₁ $
                Lemmas.length-++-≡ _ suf₀ _ suffix
                  (trans ps≡₀ (sym ps≡))
                  (trans osLen (sym strLen))
          in
          contradiction (subst (All _) (sym pre₀≡) (toWitness all<128)) all≮128
    (yes all<128) →
      return (yes
        (success pre₀ _ r₀≡
          (mk×ₚ (mkIA5StringValue (singleton os₀ refl) (fromWitness all<128)) (─ osLen))
          suf₀ ps≡₀))
  where here' = "parseIA5StringValue"

parseIA5String : Parser (Logging ∘ Dec) IA5String
parseIA5String = parseTLV _ "IA5String" _ parseIA5StringValue
