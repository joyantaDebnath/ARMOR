open import Armor.Data.Base64.TCB
open import Armor.Data.PEM.RFC5234.TCB
open import Armor.Prelude

module Armor.Data.PEM.CertText.FinalLine.TCB where

record CertFinalLine (@0 bs : List Char) : Set where
  constructor mkCertFinalLine
  field
    @0 {l e} : List Char
    line : Base64Str l
    @0 lineLen : InRange 1 64 ∘ length $ l
    eol : EOL e
    @0 bs≡ : bs ≡ l ++ e
