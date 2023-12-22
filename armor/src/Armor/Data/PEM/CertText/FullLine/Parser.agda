open import Armor.Data.Base64
open import Armor.Data.PEM.CertText.FullLine.TCB
open import Armor.Data.PEM.CertText.FullLine.Properties
open import Armor.Data.PEM.RFC5234
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.PEM.CertText.FullLine.Parser where

open Armor.Grammar.Definitions          Char
open Armor.Grammar.IList                Char
open Armor.Grammar.Parallel             Char
open Armor.Grammar.Parser               Char
open Armor.Grammar.Seq                  Char


parseCertFullLine : LogDec.MaximalParser CertFullLine
parseCertFullLine =
  LogDec.equivalent equiv
    (Seq.MaximalParser.parse&₁
      (parseIList (tell "parseCertFullLine: underflow") _
        Base64.Char.nonempty Base64.Char.nosubstrings
        parseBase64Char _)
      (Parallel.ExactLength.nosubstrings _)
      parseMaxEOL)

