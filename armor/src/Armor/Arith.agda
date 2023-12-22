open import Armor.Prelude

open import Data.Nat.Properties

module Armor.Arith where

≡⇒≤ : ∀ {m n} → m ≡ n → m ≤ n
≡⇒≤ refl = ≤-refl

divmod2 : ℕ → ℕ × Bool
divmod2 0 = 0 , false
divmod2 1 = 0 , true
divmod2 (suc (suc n)) = map₁ suc (divmod2 n)

div2 = proj₁ ∘ divmod2
mod2 = proj₂ ∘ divmod2

divmod2-≤ : ∀ n → proj₁ (divmod2 n) ≤ n
divmod2-≤ zero = ≤-refl
divmod2-≤ (suc zero) = z≤n
divmod2-≤ (suc (suc n))
  with divmod2-≤ n
...| pf = ≤-trans (s≤s pf) (s≤s (n≤1+n n))

1≤2^n : ∀ n → 1 ≤ 2 ^ n
1≤2^n zero = ≤-refl
1≤2^n (suc n) = ≤-stepsʳ ((2 ^ n) + zero) (1≤2^n n)

1≤10^n : ∀ n → 1 ≤ 10 ^ n
1≤10^n zero = ≤-refl
1≤10^n (suc n) = ≤-stepsʳ _ (1≤10^n n)

1<2^n+1 : ∀ n → 1 < 2 ^ (1 + n)
1<2^n+1 zero = s≤s (s≤s z≤n)
1<2^n+1 (suc n) = ≤-stepsʳ _ (1<2^n+1 n)

2^n≢0 : ∀ n → 2 ^ n ≢ 0
2^n≢0 n eq
  with 1≤2^n n
...| pf
  with 2 ^ n
2^n≢0 n refl | () | .0

divmod2-*2 : ∀ n → toℕ (proj₂ (divmod2 n)) + 2 * proj₁ (divmod2 n) ≡ n
divmod2-*2 zero = refl
divmod2-*2 (suc zero) = refl
divmod2-*2 (suc (suc n))
  with divmod2-*2 n
...| ih
  with divmod2 n
...| q , r = begin
  toℕ r + ((1 + q) + (1 + (q + 0))) ≡⟨ cong (toℕ r +_) (+-suc (1 + q) (q + 0)) ⟩
  toℕ r + (2 + 2 * q) ≡⟨ sym (+-assoc (toℕ r) 2 (2 * q)) ⟩
  (toℕ r + 2) + 2 * q ≡⟨ cong (_+ 2 * q) (+-comm (toℕ r) 2) ⟩
  (2 + (toℕ r)) + 2 * q ≡⟨ +-assoc 2 (toℕ r) (2 * q) ⟩
  2 + (toℕ r + 2 * q) ≡⟨ cong (2 +_) ih ⟩
  2 + n ∎
  where open ≡-Reasoning

divmod2-cancel₀ : ∀ n → divmod2 (2 * n) ≡ (n , false)
divmod2-cancel₀ zero = refl
divmod2-cancel₀ (suc n)
  with 1 + (n + (1 + n + 0))
  |    eq
  where
  open ≡-Reasoning

  eq : 1 + (n + (1 + n + 0)) ≡ 2 + (2 * n)
  eq =
    1 + (n + (1 + n + 0)) ≡⟨⟩
    1 + (n + (1 + (n + 0))) ≡⟨ cong suc (+-suc _ _) ⟩
    1 + ((1 + n) + (n + 0)) ≡⟨⟩ 
    2 + (n + (n + zero)) ∎
... | n' | refl
  with divmod2 (2 * n)
  |    divmod2-cancel₀ n
... | .n , .false | refl = refl

divmod2-cancel₁ : ∀ n → divmod2 (1 + 2 * n) ≡ (n , true)
divmod2-cancel₁ zero = refl
divmod2-cancel₁ (suc n)
  with n + suc (n + zero)
  |    x≡
  where
  x≡ : n + suc (n + zero) ≡ 1 + 2 * n
  x≡ = +-suc n (n + zero)
... | .(suc (n + (n + 0))) | refl
  with divmod2 (1 + 2 * n)
  |    divmod2-cancel₁ n
... | .(n , true) | refl = refl


  -- with (1 + 2 * suc n) | x≡
  -- where
  -- open ≡-Reasoning

  -- x≡ : 1 + 2 * suc n ≡ 2 + 2 * n
  -- x≡ = begin
  --   (1 + (n + (1 + (n + 0))) ≡⟨ cong suc (sym (+-assoc n 1 _)) ⟩
  --   1 + (n + 1 + (n + 0)) ≡⟨ cong suc (cong (_+ (n + 0)) (+-comm n 1)) ⟩
  --   1 + (1 + n + (n + 0)) ∎)
-- ... | .(suc (suc (n + (n + 0)))) | refl = {!!}
--   with divmod2 (1 + 2 * n)
--   |    divmod2-cancel n
-- ... | .n , .true | refl = {!!}
-- divmod2-cancel : ∀ n → divmod2 (2 * n) ≡ (n , 0)
-- divmod2-cancel n ? = ?

divmod2-2^ : ∀ n → proj₁ (divmod2 (2 ^ (1 + n))) ≡ 2 ^ n
divmod2-2^ n
  with divmod2-*2 (2 ^ (1 + n))
...| pf
  with help (2 ^ n)
  where
  help : ∀ n → proj₂ (divmod2 (2 * n)) ≡ false
  help zero = refl
  help (suc n) rewrite +-suc n (n + 0) = help n
...| pf₂ rewrite pf₂ = *-injective (proj₁ (divmod2 (2 * 2 ^ n))) (2 ^ n) pf
  where
  *-injective : ∀ a b → 2 * a ≡ 2 * b → a ≡ b
  *-injective zero zero eq = refl
  *-injective (suc a) (suc b) eq
    rewrite +-suc a (a + 0)
    |       +-suc b (b + 0)
    = cong suc (*-injective a b (suc-injective (suc-injective eq)))

divmod2-mono-≤ : ∀ m n → m ≤ n → proj₁ (divmod2 m) ≤ proj₁ (divmod2 n)
divmod2-mono-≤ zero n m≤n = z≤n
divmod2-mono-≤ (suc zero) (suc zero) m≤n = z≤n
divmod2-mono-≤ (suc zero) (suc (suc n)) m≤n = z≤n
divmod2-mono-≤ (suc (suc m)) (suc zero) (s≤s ())
divmod2-mono-≤ (suc (suc m)) (suc (suc n)) (s≤s (s≤s m≤n))
  with divmod2 m
  |    divmod2 n
  |    divmod2-mono-≤ m n m≤n
... | q₁ , r₁ | q₂ , r₂ | q₁≤q₂ = s≤s q₁≤q₂


divmod2-mono-< : ∀ m n → 2 + m ≤ n → div2 m < div2 n
divmod2-mono-< zero .(suc (suc _)) (s≤s (s≤s 2+m≤n)) = s≤s z≤n
divmod2-mono-< (suc zero) .(suc (suc (suc _))) (s≤s (s≤s (s≤s 2+m≤n))) = s≤s z≤n
divmod2-mono-< (suc (suc m)) (suc .(suc n)) (s≤s (s≤s{n = n} 2+m≤n))
  with div2 m
  |    div2 n
  |    divmod2-mono-< m n 2+m≤n
... | xxx | yyy | zzz = s≤s zzz

divmod2-mono-<' : ∀ m n → m < 2 * n → div2 m < n
divmod2-mono-<' zero (suc n) m<2*n = s≤s z≤n
divmod2-mono-<' (suc zero) (suc n) m<2*n = s≤s z≤n
divmod2-mono-<' (suc (suc m)) (suc n) (s≤s m<2*n)
  with n + suc (n + zero)
  |    +-suc n (n + zero)
divmod2-mono-<' (suc (suc m)) (suc n) (s≤s (s≤s m<2*n)) | .(suc (n + (n + 0))) | refl =
  s≤s (divmod2-mono-<' m n m<2*n)

infixl 7 _mod10^n_

_mod10^n_ : (m n : ℕ) → ℕ
m mod10^n n = (m % (10 ^ n)) {fromWitnessFalse (>⇒≢ (1≤10^n n))}

-- divmod2-mono-< : ∀ m n → m < n → proj₁ (divmod2 m) < proj₁ (divmod2 n)

-- divmod2-m∸n : ∀ m n → div2 (m - n) ≤ div2 m - div2 n
-- divmod2-m∸n m n
--   with m - n
--   | inspect (m -_) n
-- ... | zero | [ m-n≡ ]R
--   with m∸n≡0⇒m≤n{m = m}{n = n} m-n≡
-- ... | m≤n
--   with divmod2-mono-≤ _ _ m≤n
-- ... | m/2≤n/2 = ≡⇒≤ ∘ sym $ m≤n⇒m∸n≡0 m/2≤n/2
-- divmod2-m∸n m n | suc m-n | [ m-n≡ ]R = {!!}


-- divmod2-<-^ : ∀ i n → 2 + i < 2 ^ (1 + n) → 1 + proj₁ (divmod2 i) < 2 ^ n
-- divmod2-<-^ i zero (s≤s (s≤s ()))
-- divmod2-<-^ zero n@(suc n') i< = 1<2^n+1 n'
-- divmod2-<-^ i@1 n@(suc n') i< = 1<2^n+1 n'
-- divmod2-<-^ i@(suc (suc i')) n@(suc n') i<
--   with divmod2-mono-≤ _ _ i<
-- ... | 1+i<2^n+1 = {!!}
--   where
--   open ≤-Reasoning
--   qᵢ = proj₁ (divmod2 i)
--   qᵢ' = proj₁ (divmod2 i')
