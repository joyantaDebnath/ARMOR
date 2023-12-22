open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
open import Armor.Prelude
open import Relation.Nullary.Implication

module Armor.Data.X509.Semantic.Cert.R12 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.3
-- If the KeyCertSign bit is asserted, then the CA bit in the Basic Constraints extension MUST also be asserted.

R12 : ∀ {@0 bs} → Cert bs → Set
R12 c = T (isKeyCertSignPresent (Cert.getKU c)) → IsConfirmedCA c

r12 : ∀ {@0 bs} (c : Cert bs) → Dec (R12 c)
r12 c = T-dec →-dec (isConfirmedCA? c)
