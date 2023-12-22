{-# OPTIONS --sized-types #-}

open import Armor.Data.X509
import      Armor.Data.X509.Semantic.Chain.TCB as Chain
open import Armor.Prelude

module Armor.Data.X509.Semantic.Chain.R22 where

open Chain using (Chain)

-- https://datatracker.ietf.org/doc/html/rfc5280#section-6.1
-- A certificate MUST NOT appear more than once in a prospective certification path.

module _ {trust candidates : List (Exists─ _ Cert)} {@0 bs} (issuee : Cert bs) where

  R22 : Chain trust candidates issuee → Set
  R22 c = List.Unique _≟_ (Chain.toList c)

  r22 : Decidable R22
  r22 c = List.unique? _≟_ (Chain.toList c)

