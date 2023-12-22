open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
open import Armor.Prelude

module Armor.Data.X509.Semantic.Cert.R17 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-6.1.3 (2)
-- The certificate Validity period includes the current time

R17 : ∀ {@0 bs₁ bs₂} → Cert bs₁ → Validity.Time bs₂ → Set
R17 c t = Validity.ValidTime t (Cert.getValidity c)
  -- T (Time.lessEq (proj₂ (Cert.getValidityStartTime c)) t ∧ Time.lessEq t (proj₂ (Cert.getValidityEndTime c)))

r17 : ∀ {@0 bs₁ bs₂} → (c : Cert bs₁) → (t : Validity.Time bs₂) → Dec (R17 c t)
r17 c t = Validity.validTime? t (Cert.getValidity c)
