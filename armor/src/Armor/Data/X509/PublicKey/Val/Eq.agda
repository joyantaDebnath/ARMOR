open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg
import      Armor.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
open import Armor.Data.X509.PublicKey.Val.EC
open import Armor.Data.X509.PublicKey.Val.RSA
open import Armor.Data.X509.PublicKey.Val.TCB
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
open import Armor.Prelude

module Armor.Data.X509.PublicKey.Val.Eq where

open Armor.Grammar.Definitions UInt8

eq≋' : ∀ {@0 bs} → (a : PublicKeyAlg bs) → (d : Dec ((-, TLV.val (Alg.getOID a)) ∈ OIDs.Supported))
       → Eq≋ (PublicKeyVal' a d)
eq≋' o (yes (here px)) = it
eq≋' o (yes (there (here px))) = it
eq≋' o (no ¬p) = it

eq≋ : ∀ {@0 bs} → {a : PublicKeyAlg bs} → Eq≋ (PublicKeyVal a)
Eq≋._≋?_ (eq≋ {a = a}) v₁ v₂ =
  case Eq≋._≋?_ (eq≋' a (_ ∈? _)) v₁ v₂ ret (const _) of λ where
    (no ¬p) → no λ where ≋-refl → contradiction ≋-refl ¬p
    (yes ≋-refl) → yes ≋-refl
