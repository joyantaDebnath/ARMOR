open import Armor.Data.Base64.TCB
open import Armor.Data.PEM.CertText.FinalLine.TCB
open import Armor.Data.PEM.CertText.FullLine.TCB
import      Armor.Grammar.IList
open import Armor.Prelude

module Armor.Data.PEM.CertText.TCB where

open Armor.Grammar.IList Char

record CertText (@0 bs : List Char) : Set where
  constructor mkCertText
  field
    @0 {b f} : List Char
    body  : IList CertFullLine b
    final : CertFinalLine      f
    @0 bs≡ : bs ≡ b ++ f

