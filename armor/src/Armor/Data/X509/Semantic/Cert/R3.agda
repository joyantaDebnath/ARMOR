open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
open import Armor.Prelude

module Armor.Data.X509.Semantic.Cert.R3 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.2.2
-- The Serial number MUST be a positive integer assigned by the CA to each certificate.

R3 : ∀ {@0 bs} → Cert bs → Set
R3 c = ℤ.+ 0 ℤ.< Cert.getSerial c

r3 : ∀ {@0 bs} (c : Cert bs) → Dec (R3 c)
r3 c = (ℤ.+ 0 ℤ.<? Cert.getSerial c)
