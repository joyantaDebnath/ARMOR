open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.Properties
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.TCB
open import Armor.Data.X690-DER.Null as Null
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parser
import      Armor.Grammar.Sum
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Alg.ECPKParameters.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Sum         UInt8

parse : Parser (Logging ∘ Dec) ECPKParameters
parse = parseEquivalent equivalent (parseSum ECParameters.parse (parseSum parseOID Null.parse))
