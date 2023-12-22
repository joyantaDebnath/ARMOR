open import Armor.Binary
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X509.Name.Properties
open import Armor.Data.X509.Name.RDN
open import Armor.Data.X509.Name.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.Name.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parser      UInt8

private
  here' = "X509: Name"

parse : Parser (Logging ∘ Dec) Name
parse = RDN.parseSequence
