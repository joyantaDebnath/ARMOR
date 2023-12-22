open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
open import Armor.Prelude
open import Relation.Nullary.Implication

module Armor.Data.X509.Semantic.Cert.R18 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.3
-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.12
--- consistency of certificate purposes based on key usage bits and extended key usage OIDs
--- only for end-entity certificate

R18 : ∀ {@0 bs} → Cert bs → Set
R18 c = T (checkPurposeConsistency (Cert.getKU c) (getEKUOIDList (Cert.getEKU c)))

r18 : ∀ {@0 bs} (c : Cert bs) → Dec (R18 c)
r18 c = T-dec

