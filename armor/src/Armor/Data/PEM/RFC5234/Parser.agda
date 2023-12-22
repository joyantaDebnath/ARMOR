open import Armor.Binary
  renaming (module Base64 to B64)
open import Armor.Data.Base64
open import Armor.Data.PEM.RFC5234.TCB
import      Armor.Data.PEM.RFC5234.Properties
  as RFC5234
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parser
import      Armor.Grammar.Sum
open import Armor.Prelude

module Armor.Data.PEM.RFC5234.Parser where

open Armor.Grammar.Definitions Char
open Armor.Grammar.Parser      Char
open Armor.Grammar.Sum         Char

parseMaxEOL : LogDec.MaximalParser EOL
parseMaxEOL =
  LogDec.equivalent RFC5234.EOL.equiv
    (parseMaxSum
      (LogDec.nonnesting (λ where _ (─ refl) (─ refl) → refl)
        (parseLitE (tell "parseCRLF: EOF") silent _))
      (parseMaxSum
        (LogDec.nonnesting (λ where _ (─ refl) (─ refl) → refl)
          (parseLitE (tell "parseCR: EOF") silent _))
          (LogDec.nonnesting (λ where _ (─ refl) (─ refl) → refl)
            (parseLitE (tell "parseLF: EOF") silent _))))

