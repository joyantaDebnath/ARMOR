open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
open import Armor.Prelude
open import Relation.Nullary.Implication

module Armor.Data.X509.Semantic.Cert.R2 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.2.9
-- Extension field MUST only appear if the Version is 3(2).

R2 : ∀ {@0 bs} → Cert bs → Set
R2 c = T (isSome (proj₂ (Cert.getExtensions c))) → Cert.getVersion c ≡ TBSCert.v3

r2 : ∀ {@0 bs} (c : Cert bs) → Dec (R2 c)
r2 c = T-dec →-dec _ ≟ TBSCert.v3
