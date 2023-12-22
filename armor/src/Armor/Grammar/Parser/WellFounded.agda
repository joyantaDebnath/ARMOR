open import Armor.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Armor.Grammar.Parser.WellFounded (Σ : Set) where

open import Armor.Grammar.Parser.Core Σ

ParserWF : (M : Set → Set) (A : @0 List Σ → Set) → Set
ParserWF M A = Parserᵢ (λ xs X → (@0 _ : Acc _<_ (length xs)) → M X) A

parseWF : {M : Set → Set} {A : @0 List Σ → Set} → ParserWF M A → Parser M A
runParser (parseWF p) xs = runParser p xs (<-wellFounded (length xs))
  where open import Data.Nat.Induction
