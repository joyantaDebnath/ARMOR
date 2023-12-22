open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
open import Armor.Prelude
open import Relation.Nullary.Implication

module Armor.Data.X509.Semantic.Cert.R8 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.2.6
-- if the Subject is a CRL issuer (e.g., the Key Usage extension, is present and the value of CRLSign is TRUE),
-- then the Subject field MUST be populated with a non-empty distinguished name.

R8 : ∀ {@0 bs} → Cert bs → Set
R8 c = T (isCRLSignPresent (Cert.getKU c)) → (0 < Cert.getSubjectLen c)

r8 : ∀ {@0 bs} (c : Cert bs) → Dec (R8 c)
r8 c = T-dec →-dec 0 <? _
