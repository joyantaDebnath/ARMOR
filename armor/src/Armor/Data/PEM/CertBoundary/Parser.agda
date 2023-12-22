open import Armor.Data.Base64.TCB
open import Armor.Data.PEM.CertBoundary.Properties
open import Armor.Data.PEM.CertBoundary.TCB
open import Armor.Data.PEM.RFC5234
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parser
import      Armor.Grammar.Seq.MaximalParser
open import Armor.Prelude

module Armor.Data.PEM.CertBoundary.Parser where

open Armor.Grammar.Definitions Char
open Armor.Grammar.Parser      Char
module Seq = Armor.Grammar.Seq.MaximalParser Char

parseCertBoundary : ∀ ctrl → LogDec.MaximalParser (CertBoundary ctrl)
parseCertBoundary ctrl =
  LogDec.equivalent (equiv ctrl)
    (Seq.parse&₁
      (parseLitE (tell "parseCertBoundary: EOF") silent _)
      (λ where _ (─ refl) (─ refl) → refl)
      (LogDec.parseErased parseMaxEOL))
