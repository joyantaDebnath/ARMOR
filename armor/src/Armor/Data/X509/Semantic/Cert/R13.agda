open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
open import Armor.Prelude

module Armor.Data.X509.Semantic.Cert.R13 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2
-- A certificate MUST NOT include more than one instance of a particular Extension.

R13 : ∀ {@0 bs} → Cert bs → Set
R13 c = List.Unique _≟_ (getExtensionsOIDList (Cert.getExtensionsList c))

r13 : ∀ {@0 bs} (c : Cert bs) → Dec (R13 c)
r13 c = List.unique? _≟_ (getExtensionsOIDList (Cert.getExtensionsList c))
