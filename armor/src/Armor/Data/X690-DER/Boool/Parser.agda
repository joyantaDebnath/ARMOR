open import Armor.Binary
open import Armor.Data.X690-DER.Boool.Properties
open import Armor.Data.X690-DER.Boool.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude
-- open import Data.List.Properties
-- open import Data.Nat.Properties
--   hiding (_≟_)
-- open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X690-DER.Boool.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

private
  here' = "X690-DER: Bool"

parseValue : Parser (Logging ∘ Dec) BoolValue
runParser parseValue [] = do
  tell $ here' String.++ ": underflow"
  return ∘ no $ λ where
    (success prefix read read≡ value suffix ps≡) →
      contradiction (++-conicalˡ _ suffix ps≡) (nonempty value)
runParser parseValue (x ∷ xs)
  with x ≟ # 0
... | yes refl =
  return (yes (success [ # 0 ] _ refl (mkBoolValue false (# 0) falseᵣ refl) xs refl))
... | no x≢0
  with x ≟ # 255
... | yes refl =
  return (yes (success [ # 255 ] _ refl (mkBoolValue true (# 255) trueᵣ refl) xs refl))
... | no  x≢255 = do
  tell $ here' String.++ ": invalid boolean rep"
  return ∘ no $ λ where
    (success prefix _ _ (mkBoolValue v _ vᵣ refl) suffix ps≡) → ‼
      (case vᵣ of λ where
        falseᵣ → contradiction (∷-injectiveˡ (sym ps≡)) x≢0
        trueᵣ  → contradiction (∷-injectiveˡ (sym ps≡)) x≢255)

parse : Parser (Logging ∘ Dec) Boool
parse = parseTLV Tag.Boolean here' BoolValue
              (parseExactLength nosubstrings (tell $ here' String.++ "bad length for bool") parseValue)


-- private
--   module Test where

--     tval : List Dig
--     tval = Tag.Boolean ∷ # 1 ∷ [ # 255 ]

--     fval : List Dig
--     fval = Tag.Boolean ∷ # 1 ∷ [ # 0 ]

--     badval : List Dig
--     badval = Tag.Boolean ∷ # 1 ∷ [ # 20 ]

--     test₁ : Boool tval
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseBool tval)} tt)

--     test₂ : Boool fval
--     test₂ = Success.value (toWitness {Q = Logging.val (runParser parseBool fval)} tt)

--     test₃ : ¬ Success _ Boool badval
--     test₃ = toWitnessFalse {Q = Logging.val (runParser parseBool badval)} tt
