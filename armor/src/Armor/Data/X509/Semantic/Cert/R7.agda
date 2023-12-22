open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
open import Armor.Prelude

module Armor.Data.X509.Semantic.Cert.R7 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.9
-- Where it appears, the PathLenConstraint field MUST be greater than or equal to zero.

R7' : Exists─ (List UInt8) (Option Int) → Set
R7' (─ .[] , none) = ⊤
R7' (fst , some x) = ℤ.+ 0 ℤ.≤ Int.getVal x

R7 : ∀ {@0 bs} → Cert bs → Set
R7 c = R7' (getBCPathLen (Cert.getBC c))

r7 : ∀ {@0 bs} (c : Cert bs) → Dec (R7 c)
r7 c =
  case (getBCPathLen (Cert.getBC c)) ret (λ x → Dec (R7' x)) of λ where
    (─ .[] , none) → yes tt
    (fst , some x) → ℤ.+ 0 ℤ.≤? Int.getVal x
