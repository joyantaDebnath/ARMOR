open import Armor.Binary
open import Armor.Data.X509.GeneralNames.TCB
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint
open import Armor.Data.X509.Extension.CRLDistPoint.TCB
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.Extension.CRLDistPoint.Parser where

open Armor.Grammar.Parallel UInt8
open Armor.Grammar.Parser   UInt8

private
  here' = "X509: Extension: CRLDistPoint"

parseCRLDistFields : Parser (Logging ∘ Dec) CRLDistFields
parseCRLDistFields =
  parseTLV _ here' _
    (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow")
      (parseNonEmptySeq (here' String.++ ": elems") _ TLV.nonempty TLV.nosubstrings
        parseDistPoint))
