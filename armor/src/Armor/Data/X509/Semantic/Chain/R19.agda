{-# OPTIONS --sized-types #-}

open import Armor.Data.X509
-- open import Armor.Data.X509.Semantic.Cert.Utils
--   using (IsConfirmedCA ; isConfirmedCA?)
import      Armor.Data.X509.Semantic.Chain.TCB as Chain
open import Armor.Prelude

module Armor.Data.X509.Semantic.Chain.R19 where

open Chain using (Chain)

-- https://datatracker.ietf.org/doc/html/rfc5280#section-6.1.4 (k)
-- Conforming implementations may choose to reject all Version 1 and Version 2 intermediate CA certificates

module _ {trust candidates : List (Exists─ _ Cert)} {@0 bs} (issuee : Cert bs) where

  R19 : Chain trust candidates issuee → Set
  R19 c = All (λ where (─ _ , cert) → Cert.getVersion cert ≡ TBSCert.v3) (Chain.getIntermediates c)

  r19 : Decidable R19
  r19 c = All.all? (λ where (─ _ , cert) → _ ≟ TBSCert.v3) _
