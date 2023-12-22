open import Armor.Binary
open import Armor.Data.X509.Validity.Time.Properties
open import Armor.Data.X509.Validity.Time.TCB
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.Time.GeneralizedTime
open import Armor.Data.X690-DER.Time.UTCTime
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parser
import      Armor.Grammar.Sum
open import Armor.Prelude
open import Data.Nat.Properties

module Armor.Data.X509.Validity.Time.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Sum         UInt8

parse : Parser (Logging ∘ Dec) Time
parse =
  parseEquivalent equivalent
    (parseSum GeneralizedTime.parse UTCTime.parse)
