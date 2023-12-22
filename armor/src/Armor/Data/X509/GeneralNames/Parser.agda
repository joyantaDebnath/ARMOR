open import Armor.Binary
open import Armor.Data.X509.GeneralNames.Properties
open import Armor.Data.X509.GeneralNames.GeneralName
open import Armor.Data.X509.GeneralNames.GeneralName.Parser
open import Armor.Data.X509.GeneralNames.TCB
open import Armor.Data.X509.Name
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Sum
open import Armor.Prelude
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Armor.Data.X509.GeneralNames.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Sum         UInt8

private
  here' = "X509: GeneralNames"

parseGeneralNamesElems : ∀ n → Parser (Logging ∘ Dec) (ExactLength GeneralNamesElems n)
parseGeneralNamesElems n =
    parseBoundedSequenceOf here' _ GeneralName.nonempty GeneralName.nosubstrings parseGeneralName  n 1

parseGeneralNames : Parser (Logging ∘ Dec) GeneralNames
parseGeneralNames = parseTLV _ here' _ parseGeneralNamesElems
