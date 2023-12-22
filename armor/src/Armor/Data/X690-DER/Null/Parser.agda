open import Armor.Binary
open import Armor.Data.X690-DER.Null.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X690-DER.Null.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

private
  here' = "X690-DER: Null"

parse : Parser (Logging ∘ Dec) Null
parse =
  (parseTLV Tag.Null here' (λ x → Erased (x ≡ []))
    (parseExactLength (λ where _ (─ refl) (─ refl) → refl) (tell $ here' String.++ ": nonzero length")
      (mkParser λ xs → do
        (yes s) ← runParser (parseLit (return (Level.lift tt)) (return (Level.lift tt)) []) xs
          where no ¬p → return ∘ no $ λ where
            (success prefix read read≡ (─ v) suffix ps≡) →
              contradiction (success prefix read read≡ v suffix ps≡) ¬p
        return (yes (mapSuccess (λ eq → ─ eq) s)))))

-- private
--   module Test where

--     Null₁ : List Dig
--     Null₁ = Tag.Null ∷ [ # 0 ]

--     Badnull₂ : List Dig
--     Badnull₂ = Tag.Null ∷ # 1 ∷ [ # 0 ]

--     test₁ : Null Null₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseNull Null₁)} tt)

--     test₂ : ¬ Success _ Null Badnull₂
--     test₂ = toWitnessFalse {Q = Logging.val (runParser parseNull Badnull₂)} tt
