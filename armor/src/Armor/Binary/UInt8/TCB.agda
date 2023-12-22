open import Armor.Arith
open import Armor.Prelude
import      Data.Nat.Properties as Nat
import      Data.Sign as Sign

module Armor.Binary.UInt8.TCB where

UInt8 : Set
UInt8 = Fin (2 ^ 8)

fromℕ : (m : ℕ) {_ : True (suc (toℕ m) Nat.≤? 256)} → UInt8
fromℕ m {m<} = #_ m {m<n = m<}

-- calculate octet string value as an unsigned (non-negative) integer
unsigned : List UInt8 → ℕ
unsigned [] = 0
unsigned (x ∷ bs) = toℕ x * (256 ^ length bs) + unsigned bs

-- calculate octet string value as a signed integer
twosComplement- : UInt8 → List UInt8 → ℤ
twosComplement- b bs =
  Sign.- ℤ.◃
    (  128 * 256 ^ length bs
     - unsigned
         (Fin.fromℕ<{m = toℕ b - 128}{n = 256}
           (Nat.≤-trans (s≤s (Nat.m∸n≤m (toℕ b) 128)) (Fin.toℕ<n b)) ∷ bs))

twosComplement : List UInt8 → ℤ
twosComplement [] = ℤ.+ 0
twosComplement xs@(b₁ ∷ bs) with toℕ b₁ Nat.≤? 127
... | no ¬p = twosComplement- b₁ bs
... | yes p = ℤ.+ unsigned xs

TwosComplementMinRep : UInt8 → List UInt8 → Set
TwosComplementMinRep bₕ [] = ⊤
TwosComplementMinRep bₕ (b ∷ bₜ) =
  (toℕ bₕ > 0 ⊎ toℕ bₕ ≡ 0 × toℕ b ≥ 128) × (toℕ bₕ < 255 ⊎ toℕ bₕ ≡ 255 × toℕ b ≤ 127)

-- Converts ASCII codes for '0'-'9' to the corresponding nat.
asciiNum₁ : UInt8 → ℕ
asciiNum₁ = (_- toℕ '0') ∘ toℕ

asciiNum : List UInt8 → ℕ
asciiNum [] = 0
asciiNum (x ∷ xs) = asciiNum₁ x * (10 ^ length xs) + asciiNum xs

-- Print natural number as ASCII with fixed-width
showFixed₁ : ℕ → Σ UInt8 (InRange '0' '9')
showFixed₁ n = c₁“ , ir'
  where
  module ≤ = Nat.≤-Reasoning

  c₁ : Fin 10
  c₁ = n mod 10

  c₁' = Fin.raise (toℕ '0') c₁

  c₁“ : UInt8
  c₁“ = Fin.inject≤ c₁' (toWitness{Q = _ Nat.≤? _} tt)

  ir : InRange '0' '9' c₁'
  proj₁ ir = ≤.begin
    48 ≤.≤⟨ Nat.m≤m+n 48 (toℕ c₁) ⟩
    48 + toℕ c₁ ≤.≡⟨⟩
    toℕ c₁' ≤.∎
  proj₂ ir = ≤.begin
    toℕ c₁' ≤.≡⟨⟩
    48 + toℕ c₁ ≤.≤⟨ Nat.+-monoʳ-≤ 48 (Fin.toℕ≤pred[n] c₁) ⟩
    57 ≤.∎

  ir' : InRange '0' '9' c₁“
  ir' = subst₀ (λ x → toℕ '0' ≤ x × x ≤ toℕ '9') (sym (Fin.toℕ-inject≤ c₁' (toWitness{Q = _ Nat.≤? _} tt))) ir

showFixed' : (w n : ℕ) → Σ (List UInt8) λ bs → length bs ≡ w × All (InRange '0' '9') bs
showFixed' zero n = [] , (refl , All.[])
showFixed' w@(suc w') n =
  let (c₁ , ir) = showFixed₁ quotient in
  (c₁ ∷ cs) , (cong suc len≡) , (ir ∷ irs)
  where
  open DivMod ((n divMod 10 ^ w'){fromWitnessFalse (Nat.>⇒≢ (1≤10^n w'))})
  ih = showFixed' w' (toℕ remainder)
  cs = proj₁ ih
  len≡ = proj₁ (proj₂ ih)
  irs  = proj₂ (proj₂ ih)

showFixed : (w n : ℕ) → List UInt8
showFixed w n = proj₁ (showFixed' w n)
