open import Armor.Data.Base64.TCB
open import Armor.Data.PEM.RFC5234.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Parallel
open import Armor.Prelude

module Armor.Data.PEM.CertText.FullLine.TCB where

open Armor.Grammar.Definitions Char
open Armor.Grammar.IList       Char
open Armor.Grammar.Parallel    Char

record CertFullLine (@0 bs : List Char) : Set where
  constructor mkCertFullLine
  field
    @0 {l e} : List Char
    line : ExactLength (IList Base64Char) 64 l
    eol  : EOL e
    @0 bs≡  : bs ≡ l ++ e

