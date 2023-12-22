{-# OPTIONS --sized-types #-}

open import Armor.Data.X509
open import Armor.Data.X509.Semantic.Cert.Utils
  using (IsConfirmedCA ; isConfirmedCA?)
open import Armor.Data.X509.Semantic.Chain.TCB
open import Armor.Prelude

module Armor.Data.X509.Semantic.Chain.R23 where

{- https://datatracker.ietf.org/doc/html/rfc5280#section-6.1.4
--    To prepare for processing of certificate i+1, perform the
--    following steps for certificate i:
--
--    ...
-- 
--    (k)  If certificate i is a version 3 certificate, verify that the
--         basicConstraints extension is present and that cA is set to
--         TRUE.  (If certificate i is a version 1 or version 2
--         certificate, then the application MUST either verify that
--         certificate i is a CA certificate through out-of-band means
--         or reject the certificate.  Conforming implementations may
--         choose to reject all version 1 and version 2 intermediate
--         certificates.)
-}

module _ {trust candidates : List (Exists─ _ Cert)} {@0 bs} (issuee : Cert bs) where

  R23 : Chain trust candidates issuee → Set
  R23 c = All (IsConfirmedCA ∘ proj₂) (tailSafe (toList c) (toListLength≥1 c))

  r23 : (c : Chain trust candidates issuee) → Dec (R23 c)
  r23 c = All.all? (isConfirmedCA? ∘ proj₂) _
