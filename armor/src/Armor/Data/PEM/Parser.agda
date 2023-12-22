open import Armor.Binary
  renaming (module Base64 to B64)
open import Armor.Data.Base64
open import Armor.Data.PEM.CertBoundary
open import Armor.Data.PEM.CertText
open import Armor.Data.PEM.CertText.FinalLine
open import Armor.Data.PEM.CertText.FullLine
open import Armor.Data.PEM.RFC5234
open import Armor.Data.PEM.Properties
open import Armor.Data.PEM.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Parser
import      Armor.Grammar.Seq
open import Armor.Prelude
import      Data.List.Relation.Unary.Any.Properties as Any

module Armor.Data.PEM.Parser where

open Armor.Grammar.Definitions          Char
open Armor.Grammar.IList                Char
open Armor.Grammar.Parser               Char
open Armor.Grammar.Seq                  Char

parseCert : LogDec.MaximalParser Cert
parseCert =
  LogDec.equivalent equiv
    (Seq.MaximalParser.parse&
      (parseCertBoundary "BEGIN")
      (Seq.MaximalParser.parse&
        parseMaxCertText
        (parseCertBoundary "END")
        noOverlapTextFooter)
      noOverlapHeaderText)

parseCertList : LogDec.MaximalParser CertList
parseCertList =
  parseIListMaxNoOverlap.parseIListMax
    (tell "PEM: underflow reading cert list")
    Cert nonempty noOverlap
    parseCert

-- parseCertListWithRootStore : LogDec.MaximalParser CertListWithRootStore
-- parseCertListWithRootStore = LogDec.equivalent {!!}
--                                (LogDec.parse& parseCertList (
--                                  LogDec.parse& {!!} parseCertList {!!}) {!!})
