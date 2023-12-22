open import Armor.Arith
open import Armor.Prelude
open import Data.Nat.Properties as Nat
  hiding (_≟_)
import      Data.Vec.Properties as Vec

module Armor.Binary.Bits.TCB where

Binary = Vec Bool

pattern #0 = false
pattern #1 = true

module ToBinary where
  aux : (n : ℕ) (i : ℕ) → Binary n
  aux 0 i = []
  aux (suc n) i
    with divmod2 i
  ... | q , r = r ∷ aux n q

  toBinary : ∀ {n} → Fin (2 ^ n) → Binary n
  toBinary{n} i = Vec.reverse $ aux n (toℕ i)

open ToBinary public using (toBinary)

module FromBinary where

  aux : ∀ {n} → Vec Bool n → Fin (2 ^ n)
  aux {.0} [] = Fin.zero
  aux {n@.(suc _)} (#0 ∷ bits) =
    subst Fin (suc[pred[n]]≡n {2 ^ n} (2^n≢0 n)) (Fin.inject₁ (Fin.2* (aux bits)))
  aux {n@.(suc _)} (#1 ∷ bits) =
    subst Fin (suc[pred[n]]≡n{2 ^ n} (2^n≢0 n)) (Fin.fromℕ 1 Fin.+ (Fin.2* (aux bits)))

  fromBinary : ∀ {n} → Binary n → Fin (2 ^ n)
  fromBinary bits = aux (Vec.reverse bits)

open FromBinary public using (fromBinary)

