open import Armor.Arith
open import Armor.Binary.UInt8.TCB
open import Armor.Prelude
open import Data.Fin.Properties as Fin
  hiding (_≟_)
open import Data.Nat.Properties as Nat
  hiding (_≟_)
import      Data.Sign as Sign

module Armor.Binary.UInt8.Properties where

-- unsigned
--------------------------------------------------

unsigned< : ∀ bs → unsigned bs < 256 ^ length bs
unsigned< [] = s≤s z≤n
unsigned< (x ∷ bs) = ≤.begin
  suc (toℕ x * (256 ^ length bs)) + unsigned bs ≤.≡⟨ sym (Nat.+-suc _ (unsigned bs)) ⟩
  (toℕ x * (256 ^ length bs)) + suc (unsigned bs)
    ≤.≤⟨ Nat.+-monoʳ-≤ ((toℕ x * (256 ^ length bs))) ih ⟩
  (toℕ x * (256 ^ length bs)) + 256 ^ length bs
    ≤.≡⟨ cong (_+ (256 ^ length bs))
           (Lemmas.m*n≡[suc-m]*n∸n (toℕ x) (256 ^ length bs)
             (Nat.n≢0⇒n>0 (λ eq → contradiction (Nat.m^n≡0⇒m≡0 256 (length bs) eq) λ ()))) ⟩
  suc (toℕ x) * (256 ^ length bs) - (256 ^ length bs) + 256 ^ length bs
    ≤.≤⟨ Nat.+-monoˡ-≤ (256 ^ length bs){x = suc (toℕ x) * (256 ^ length bs) - (256 ^ length bs)}
           (Nat.∸-monoˡ-≤ {m = suc (toℕ x) * (256 ^ length bs)} (256 ^ length bs)
              (Nat.*-monoˡ-≤ (256 ^ length bs) {x = suc (toℕ x)} (Fin.toℕ<n x))) ⟩ 
  (256 ^ (1 + length bs)) - (256 ^ length bs) + 256 ^ length bs
    ≤.≡⟨ Nat.m∸n+n≡m
           ((256 ^ length bs) ≤ 256 * (256 ^ length bs)
           ∋ ≤.begin
             256 ^ length bs ≤.≡⟨ sym (Nat.*-identityˡ _) ⟩
             1 * (256 ^ length bs) ≤.≤⟨ Nat.*-monoˡ-≤ (256 ^ length bs) (s≤s{n = 255} z≤n) ⟩
             256 * 256 ^ length bs ≤.∎) ⟩
  256 ^ (1 + length bs) ≤.∎
  where
  module ≤ = Nat.≤-Reasoning

  ih : unsigned bs < 256 ^ length bs
  ih = unsigned< bs

unsigned-head< : ∀ b bs {n} → toℕ b < n → unsigned (b ∷ bs) < n * 256 ^ length bs
unsigned-head< b bs {n} b≤n = ≤.begin
  suc (unsigned (b ∷ bs)) ≤.≡⟨⟩
  suc (toℕ b * 256 ^ length bs + unsigned bs) ≤.≡⟨ sym (Nat.+-suc _ _) ⟩
  toℕ b * 256 ^ length bs + suc (unsigned bs) ≤.≤⟨ Nat.+-monoʳ-≤ (toℕ b * 256 ^ length bs) (unsigned< bs) ⟩
  toℕ b * 256 ^ length bs + 256 ^ length bs ≤.≡⟨ Nat.+-comm _ (256 ^ length bs) ⟩
  256 ^ length bs + toℕ b * 256 ^ length bs ≤.≡⟨⟩
  (1 + toℕ b) * 256 ^ length bs ≤.≤⟨ Nat.*-monoˡ-≤ _ b≤n ⟩
  n * 256 ^ length bs ≤.∎
  where
  module ≤ = Nat.≤-Reasoning

unsigned-leading-0
  : ∀ {bs₁ bs₂} → (ne : 0 < length bs₂) (l : length bs₁ < length bs₂) → unsigned bs₁ ≡ unsigned bs₂
    → toℕ (headSafe bs₂ ne) ≡ 0
unsigned-leading-0 {bs₁} {Fin.zero ∷ bs₂} ne l eq = refl
unsigned-leading-0 {bs₁} {Fin.suc x ∷ bs₂} (s≤s z≤n) (s≤s l) eq =
  contradiction eq (Nat.<⇒≢ (≤.begin
    suc (unsigned bs₁) ≤.≤⟨ unsigned< bs₁ ⟩
    256 ^ length bs₁ ≤.≤⟨ Lemmas.^-monoʳ-≤ 256 (s≤s{n = 255} z≤n) l ⟩
    256 ^ length bs₂ ≤.≤⟨ Nat.m≤m+n (256 ^ length bs₂) _ ⟩
    256 ^ length bs₂ + toℕ x * (256 ^ length bs₂)
      ≤.≤⟨ Nat.m≤m+n _ (unsigned bs₂) ⟩
    256 ^ length bs₂ + toℕ x * (256 ^ length bs₂) + unsigned bs₂ ≤.∎))
  where
  module ≤ = Nat.≤-Reasoning

unsigned-injective : ∀ bs₁ bs₂ → length bs₁ ≡ length bs₂ → unsigned bs₁ ≡ unsigned bs₂ → bs₁ ≡ bs₂
unsigned-injective [] [] len≡ eq = refl
unsigned-injective (x₁ ∷ bs₁) (x₂ ∷ bs₂) len≡ eq =
  cong₂ _∷_ x₁≡x₂ bs₁≡bs₂
  where
  module ≤ = Nat.≤-Reasoning
  open ≡-Reasoning

  len≡' = Nat.suc-injective len≡

  lem₀ : ∀ (x₁ x₂ : UInt8) bs₁ bs₂ → length bs₁ ≡ length bs₂
         → toℕ x₁ < toℕ x₂
         → toℕ x₁ * (256 ^ length bs₁) + unsigned bs₁ ≡ toℕ x₂ * (256 ^ length bs₁) + unsigned bs₂
         → ⊥
  lem₀ x₁ x₂ bs₁ bs₂ len≡ x₁<x₂ eq
    with Lemmas.m≤n⇒∃[o]o+m≡n x₁<x₂
  ... | (o , x₁+o≡x₂) rewrite sym x₁+o≡x₂ =
    contradiction eq (Nat.<⇒≢ (≤.begin
      1 + (toℕ x₁ * (256 ^ length bs₁)) + unsigned bs₁ ≤.≡⟨ sym (Nat.+-suc _ (unsigned bs₁)) ⟩
      toℕ x₁ * (256 ^ length bs₁) + suc (unsigned bs₁) ≤.≤⟨ Nat.+-monoʳ-≤ (toℕ x₁ * 256 ^ length bs₁) (unsigned< bs₁) ⟩
      toℕ x₁ * (256 ^ length bs₁) + 256 ^ (length bs₁) ≤.≡⟨ Nat.+-comm (toℕ x₁ * 256 ^ length bs₁) (256 ^ length bs₁) ⟩
      (1 + toℕ x₁) * 256 ^ length bs₁ ≤.≤⟨ Nat.*-monoˡ-≤ (256 ^ length bs₁) (Nat.m≤n+m (1 + toℕ x₁) o) ⟩
      (o + suc (toℕ x₁)) * 256 ^ length bs₁ ≤.≤⟨ Nat.m≤m+n _ (unsigned bs₂) ⟩
      (o + suc (toℕ x₁)) * 256 ^ length bs₁ + unsigned bs₂ ≤.∎))

  x₁≡x₂ : x₁ ≡ x₂
  x₁≡x₂
    with Nat.<-cmp (toℕ x₁) (toℕ x₂)
  ... | tri< x₁<x₂ _ _ =
    ⊥-elim (lem₀ x₁ x₂ bs₁ bs₂ len≡' x₁<x₂
      (subst (λ n → toℕ x₁ * (256 ^ length bs₁) + unsigned bs₁ ≡ toℕ x₂ * (256 ^ n) + unsigned bs₂)
         (sym len≡') eq))
  ... | tri> _ _ x₂<x₁ =
   ⊥-elim (lem₀ x₂ x₁ bs₂ bs₁ (sym len≡') x₂<x₁
      (subst (λ n → toℕ x₂ * (256 ^ length bs₂) + unsigned bs₂ ≡ toℕ x₁ * (256 ^ n) + unsigned bs₁)
         len≡' (sym eq)))
  ... | tri≈ _ x₁≡x₂ _ = Fin.toℕ-injective x₁≡x₂

  bs₁≡bs₂ : bs₁ ≡ bs₂
  bs₁≡bs₂ = unsigned-injective bs₁ bs₂ (Nat.suc-injective len≡)
         (Nat.+-cancelˡ-≡ (toℕ x₁ * 256 ^ length bs₁) (begin
           toℕ x₁ * 256 ^ length bs₁ + unsigned bs₁ ≡⟨ eq ⟩
           toℕ x₂ * 256 ^ length bs₂ + unsigned bs₂
             ≡⟨ cong (_+ unsigned bs₂)
                  (cong₂ _*_
                    (cong Fin.toℕ (sym x₁≡x₂))
                    (cong (256 ^_) (sym $ Nat.suc-injective len≡))) ⟩
           toℕ x₁ * 256 ^ length bs₁ + unsigned bs₂ ∎))

-- twosComplement
--------------------------------------------------
twosComplementMinRep? : ∀ bₕ bₜ → Dec (TwosComplementMinRep bₕ bₜ)
twosComplementMinRep? bₕ [] = yes tt
twosComplementMinRep? bₕ (b ∷ bₜ) =
  case toℕ bₕ ≟ 0 of λ where
    (yes bₕ≡0) → case toℕ b ≥? 128 of λ where
      (yes b≥128) → yes ((inj₂ (bₕ≡0 , b≥128)) , (inj₁ (subst (_< 255) (sym bₕ≡0) (s≤s z≤n))))
      (no ¬b≥128) → no λ where
        (inj₁ bₕ>0 , _) → contradiction bₕ≡0 (Nat.>⇒≢ bₕ>0)
        (inj₂ (_ , b≥128) , _) → contradiction b≥128 ¬b≥128
    (no ¬bₕ≡0) →
      let bₕ>0 : toℕ bₕ > 0
          bₕ>0 = Nat.≤∧≢⇒< z≤n (¬bₕ≡0 ∘′ sym)
      in
      case toℕ bₕ ≟ 255 of λ where
        (yes bₕ≡255) → case toℕ b Nat.≤? 127 of λ where
          (yes b≤127) → yes ((inj₁ bₕ>0) , (inj₂ (bₕ≡255 , b≤127)))
          (no ¬b≤127) → no λ where
            (_ , inj₁ bₕ<255) → contradiction bₕ≡255 (Nat.<⇒≢ bₕ<255)
            (_ , inj₂ (_ , b≤127)) → contradiction b≤127 ¬b≤127
        (no ¬bₕ≡255) → yes ((inj₁ bₕ>0) , (inj₁ (Nat.≤∧≢⇒< (Nat.+-cancelˡ-≤ 1 (Fin.toℕ<n bₕ)) ¬bₕ≡255)))

uniqueTwosCompletementMinRep : ∀ bₕ bₜ → Unique (TwosComplementMinRep bₕ bₜ)
uniqueTwosCompletementMinRep bₕ [] tt tt = refl
uniqueTwosCompletementMinRep bₕ (b ∷ bₜ) (mr₁₁ , mr₁₂) (mr₂₁ , mr₂₂) =
  case ⊎-unique Nat.≤-irrelevant (×-unique ≡-unique Nat.≤-irrelevant)
         (λ where (bₕ>0 , bₕ≡0 , _) → contradiction bₕ≡0 (Nat.>⇒≢ bₕ>0))
         mr₁₁ mr₂₁
  of λ where
    refl → case ⊎-unique Nat.≤-irrelevant (×-unique ≡-unique Nat.≤-irrelevant)
                  (λ where (bₕ<255 , bₕ≡255 , _) → contradiction bₕ≡255 (Nat.<⇒≢ bₕ<255))
                  mr₁₂ mr₂₂
           of λ where
      refl → refl

twosComplement<0 : ∀ b bs → ∃ λ n → twosComplement- b bs ≡ ℤ.-[1+ n ]
twosComplement<0 b bs = _ , cong (λ x → Sign.- ℤ.◃ x) (begin
    128 * 256 ^ length bs - (toℕ b' * 256 ^ length bs + unsigned bs)
      ≡⟨ sym (∸-+-assoc (128 * 256 ^ length bs) (toℕ b' * 256 ^ length bs) (unsigned bs)) ⟩
    128 * 256 ^ length bs - (toℕ b' * 256 ^ length bs) - unsigned bs
      ≡⟨ cong (_- (unsigned bs)) (sym (Nat.*-distribʳ-∸ (256 ^ length bs) 128 (toℕ b'))) ⟩
    (128 - toℕ b') * 256 ^ length bs - unsigned bs
      ≡⟨ cong (λ x → x * (256 ^ length bs) ∸ unsigned bs) (proj₂ diff) ⟩
    suc (proj₁ diff) * 256 ^ length bs - unsigned bs
      ≡⟨⟩
    256 ^ length bs + (proj₁ diff * 256 ^ length bs) - unsigned bs
      ≡⟨ cong (_∸ unsigned bs) (+-comm (256 ^ length bs) (proj₁ diff * 256 ^ length bs)) ⟩
    (proj₁ diff * 256 ^ length bs) + 256 ^ length bs - unsigned bs
      ≡⟨ +-∸-assoc (proj₁ diff * (256 ^ length bs)){n = 256 ^ length bs}{o = unsigned bs} (<⇒≤ (unsigned< bs)) ⟩
    (proj₁ diff * 256 ^ length bs) + (256 ^ length bs - unsigned bs)
      ≡⟨ cong (proj₁ diff * (256 ^ length bs) +_) (proj₂ diff') ⟩
    (proj₁ diff * 256 ^ length bs) + suc (proj₁ diff')
      ≡⟨ +-suc _ (proj₁ diff') ⟩
    suc (proj₁ diff * 256 ^ length bs) + proj₁ diff' ∎)
  where
  open ≡-Reasoning
  module ≤ = ≤-Reasoning

  b-128<256 : toℕ b - 128 < 256
  b-128<256 = Nat.≤-trans (s≤s (m∸n≤m (toℕ b) 128)) (Fin.toℕ<n b)

  b' : UInt8
  b' = Fin.fromℕ< b-128<256

  b'≤127 : toℕ b' ≤ 127
  b'≤127 = ≤.begin
    toℕ b' ≤.≡⟨⟩
    toℕ (Fin.fromℕ< b-128<256) ≤.≡⟨ toℕ-fromℕ< b-128<256 ⟩
    toℕ b - 128 ≤.≤⟨ ∸-monoˡ-≤ {m = toℕ b} {n = 255} 128 (+-cancelˡ-≤ 1 (Fin.toℕ<n b)) ⟩
    127 ≤.∎

  diff : ∃ λ n → 128 - toℕ b' ≡ suc n
  diff with Lemmas.m≤n⇒∃[o]o+m≡n b'≤127
  ... | (o , o+b≡127) = o , (begin
    128 - toℕ b' ≡⟨ cong (λ x → suc x - toℕ b') (sym o+b≡127) ⟩
    suc o + toℕ b' - toℕ b' ≡⟨ m+n∸n≡m (suc o) (toℕ b') ⟩
    suc o ∎)

  diff' : ∃ λ n → 256 ^ length bs - unsigned bs ≡ suc n
  diff' with Lemmas.m≤n⇒∃[o]o+m≡n (unsigned< bs)
  ... | (o , o+[1+u]≡) = o , (begin
    256 ^ length bs - unsigned bs ≡⟨ cong (_- (unsigned bs)) (sym o+[1+u]≡) ⟩
    o + suc (unsigned bs) - unsigned bs ≡⟨ cong (_∸ unsigned bs) (+-suc o (unsigned bs)) ⟩
    suc o + unsigned bs - unsigned bs ≡⟨ m+n∸n≡m (suc o) (unsigned bs) ⟩
    suc o ∎)

¬twosComplementMinRep : ∀ bₕ₁ bₜ₁ bₕ₂ bₜ₂ → length bₜ₁ < length bₜ₂ → twosComplement (bₕ₁ ∷ bₜ₁) ≡ twosComplement (bₕ₂ ∷ bₜ₂)
                        → ¬ TwosComplementMinRep bₕ₂ bₜ₂
¬twosComplementMinRep bₕ₁ bₜ₁ bₕ₂ (b ∷ bₜ₂) (s≤s bs₁<bs₂) eq (mr₂₁ , mr₂₂)
  with toℕ bₕ₁ Nat.≤? 127
... | yes bₕ₁≤127
  with toℕ bₕ₂ Nat.≤? 127
... | no ¬bₕ₂≤127 =
  contradiction {P = ℤ.+ _ ≡ ℤ.-[1+ _ ]} (trans eq (proj₂ (twosComplement<0 bₕ₂ (b ∷ bₜ₂)))) (λ ())
... | yes bₕ₂≤127 =
  contradiction lem₀ (Nat.<⇒≢ (≤.begin
    suc (toℕ bₕ₁ * 256 ^ length bₜ₁) + unsigned bₜ₁
      ≤.≡⟨ sym (+-suc _ (unsigned bₜ₁)) ⟩
    toℕ bₕ₁ * 256 ^ length bₜ₁ + suc (unsigned bₜ₁)
      ≤.≤⟨ +-monoʳ-≤ _ (unsigned< bₜ₁) ⟩
    toℕ bₕ₁ * 256 ^ length bₜ₁ + 256 ^ length bₜ₁
      ≤.≡⟨ +-comm _ (256 ^ length bₜ₁) ⟩
    suc (toℕ bₕ₁) * 256 ^ length bₜ₁
      ≤.≤⟨ Nat.*-monoʳ-≤ (suc (toℕ bₕ₁)) (Lemmas.^-monoʳ-≤ 256 (s≤s z≤n) bs₁<bs₂) ⟩
    suc (toℕ bₕ₁) * 256 ^ length bₜ₂
      ≤.≤⟨ (case singleton (toℕ bₕ₂) refl ret (const _) of λ where
        (singleton (suc n) n≡) → ≤.begin
          suc (toℕ bₕ₁) * 256 ^ length bₜ₂
            ≤.≤⟨ *-monoˡ-≤ (256 ^ length bₜ₂) (Fin.toℕ<n bₕ₁) ⟩
          256 ^ (1 + length bₜ₂)
            ≤.≤⟨ Nat.m≤n*m (256 ^ (1 + length bₜ₂)) {toℕ bₕ₂} (n≢0⇒n>0 (λ eq → case trans (‼ n≡) eq of λ ())) ⟩
          toℕ bₕ₂ * 256 ^ (1 + length bₜ₂)
            ≤.≤⟨ m≤m+n _ _ ⟩
          toℕ bₕ₂ * 256 ^ (1 + length bₜ₂) + (toℕ b * 256 ^ length bₜ₂ + unsigned bₜ₂)
            ≤.∎
        (singleton zero    n≡) → ≤.begin
          suc (toℕ bₕ₁) * 256 ^ length bₜ₂
            ≤.≤⟨ *-monoˡ-≤ (256 ^ length bₜ₂) (Nat.≤-trans (s≤s bₕ₁≤127) ([_,_]′ (λ x → contradiction (‼ sym n≡) (Nat.>⇒≢ x )) proj₂ mr₂₁ )
            ) ⟩
          toℕ b * 256 ^ length bₜ₂
            ≤.≤⟨ m≤m+n _ (unsigned bₜ₂) ⟩
          toℕ b * 256 ^ length bₜ₂ + unsigned bₜ₂
            ≤.≡⟨ cong (λ x → x * 256 ^ (1 + length bₜ₂) + (toℕ b * (256 ^ length bₜ₂) + unsigned bₜ₂))
                   (‼ n≡) ⟩
          toℕ bₕ₂ * 256 ^ (1 + length bₜ₂) + (toℕ b * 256 ^ length bₜ₂ + unsigned bₜ₂)
            ≤.∎)⟩
    toℕ bₕ₂ * 256 ^ (1 + length bₜ₂) + (toℕ b * 256 ^ length bₜ₂ + unsigned bₜ₂) ≤.∎))
  where
  module ≤ = ≤-Reasoning
  import Data.Integer.Properties as ℤ

  lem₀ : toℕ bₕ₁ * (256 ^ length bₜ₁) + unsigned bₜ₁ ≡ toℕ bₕ₂ * 256 ^ (1 + length bₜ₂) + (toℕ b * 256 ^ length bₜ₂ + unsigned bₜ₂)
  lem₀ = ℤ.+-injective eq
¬twosComplementMinRep bₕ₁ bₜ₁ bₕ₂ (b ∷ bₜ₂) (s≤s bs₁<bs₂) eq (mr₂₁ , mr₂₂) | no ¬bₕ₁≤127
  with toℕ bₕ₂ Nat.≤? 127
... | yes bₕ₂≤127 =
  contradiction {P = ℤ.+ _ ≡ ℤ.-[1+ _ ]} (trans (sym eq) (proj₂ (twosComplement<0 bₕ₁ bₜ₁))) (λ ())
... | no ¬bₕ₂≤127 =
  contradiction lem₀ (Nat.<⇒≢ (≤.begin
    suc (128 * 256 ^ length bₜ₁ - unsigned (bₕ₁' ∷ bₜ₁))
      ≤.≤⟨ +-monoʳ-≤ 1 (≤.begin
             128 * 256 ^ length bₜ₁ - unsigned (bₕ₁' ∷ bₜ₁) ≤.≤⟨ m∸n≤m _ (unsigned (bₕ₁' ∷ bₜ₁)) ⟩
             128 * 256 ^ length bₜ₁ ≤.≤⟨ *-monoʳ-≤ 128 (Lemmas.^-monoʳ-≤ 256 (s≤s z≤n) bs₁<bs₂) ⟩
             128 * 256 ^ length bₜ₂ ≤.≡⟨ *-distribʳ-∸ (256 ^ length bₜ₂) 256 128 ⟩
             256 ^ (1 + length bₜ₂) - 128 * 256 ^ length bₜ₂
               ≤.≡⟨ cong (_∸ 128 * (256 ^ length bₜ₂)) (begin
                 256 ^ (1 + length bₜ₂) ≡⟨ sym (*-identityˡ (256 ^ (1 + length bₜ₂))) ⟩
                 1 * 256 ^ (1 + length bₜ₂) ≡⟨⟩
                 (128 - 127) * 256 ^ (1 + length bₜ₂) ≡⟨ *-distribʳ-∸ (256 ^ (1 + length bₜ₂) ) 128 127 ⟩
                 128 * 256 ^ (1 + length bₜ₂) - 127 * 256 ^ (1 + length bₜ₂) ∎) ⟩
             (128 * 256 ^ (1 + length bₜ₂) - 127 * 256 ^ (1 + length bₜ₂)) - 128 * 256 ^ length bₜ₂
               ≤.≡⟨ ∸-+-assoc (128 * 256 ^ (1 + length bₜ₂)) (127 * 256 ^ (1 + length bₜ₂)) (128 * 256 ^ length bₜ₂) ⟩
             128 * 256 ^ (1 + length bₜ₂) - (127 * 256 ^ (1 + length bₜ₂) + 128 * 256 ^ length bₜ₂) ≤.∎) ⟩
    suc (128 * 256 ^ (1 + length bₜ₂) - (127 * 256 ^ (1 + length bₜ₂) + 128 * 256 ^ length bₜ₂))
      ≤.≤⟨ ∸-monoʳ-<
             {128 * 256 ^ (1 + length bₜ₂)}
             {(127 * 256 ^ (1 + length bₜ₂) + 128 * 256 ^ length bₜ₂)}
             {toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + (toℕ b * 256 ^ length bₜ₂ + unsigned bₜ₂)}
             (case toℕ bₕ₂ ≟ 255 ret (const _) of λ where
               (yes bₕ₂≡255) → lem₂ bₕ₂≡255
               (no  bₕ₂≢255) → lem₁ (+-cancelˡ-≤ 1 (Nat.≤∧≢⇒< (+-cancelˡ-≤ 1 (Fin.toℕ<n bₕ₂)) bₕ₂≢255)))
             (≤.begin
               127 * 256 ^ (1 + length bₜ₂) + 128 * (256 ^ length bₜ₂)
                 ≤.≤⟨ +-monoʳ-≤ (127 * 256 ^ (1 + length bₜ₂)) (*-monoˡ-≤ (256 ^ length bₜ₂) (toWitness{Q = 128 Nat.≤? 256} tt)) ⟩
               127 * 256 ^ (1 + length bₜ₂) + 256 ^ (1 + length bₜ₂)
                 ≤.≡⟨ +-comm (127 * 256 ^ (1 + length bₜ₂)) (256 ^ (1 + length bₜ₂)) ⟩
               128 * 256 ^ (1 + length bₜ₂) ≤.∎) ⟩
    128 * 256 ^ (1 + length bₜ₂) - (toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + (toℕ b * 256 ^ length bₜ₂ + unsigned bₜ₂)) ≤.∎))
  where
  open ≡-Reasoning
  module ≤ = ≤-Reasoning
  bₕ₁∸128<256 = Nat.≤-trans (s≤s (m∸n≤m (toℕ bₕ₁) 128)) (Fin.toℕ<n bₕ₁)
  bₕ₂∸128<256 = Nat.≤-trans (s≤s (m∸n≤m (toℕ bₕ₂) 128)) (Fin.toℕ<n bₕ₂)

  bₕ₁' = Fin.fromℕ<{m = toℕ bₕ₁ - 128}{n = 256} bₕ₁∸128<256
  bₕ₂' = Fin.fromℕ<{m = toℕ bₕ₂ - 128}{n = 256} bₕ₂∸128<256

  bₕ₂'≤127 : toℕ bₕ₂' ≤ 127
  bₕ₂'≤127 = ≤.begin
    toℕ bₕ₂' ≤.≡⟨⟩
    toℕ (Fin.fromℕ<{m = toℕ bₕ₂ - 128}{n = 256} bₕ₂∸128<256) ≤.≡⟨ Fin.toℕ-fromℕ< bₕ₂∸128<256 ⟩
    toℕ bₕ₂ - 128 ≤.≤⟨ ∸-monoˡ-≤ 128 (+-cancelˡ-≤ 1 (Fin.toℕ<n bₕ₂)) ⟩
    127 ≤.∎

  lem₀ :   128 * 256 ^ length bₜ₁ - unsigned (bₕ₁' ∷ bₜ₁)
         ≡ 128 * 256 ^ (1 + length bₜ₂) - (toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + (toℕ b * 256 ^ length bₜ₂ + unsigned bₜ₂))
  lem₀ = Lemmas.neg◃-injective eq

  lem₁ : toℕ bₕ₂ ≤ 254 →   toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + unsigned (b ∷ bₜ₂)
                         < 127      * 256 ^ (1 + length bₜ₂) + 128 * 256 ^ length bₜ₂
  lem₁ bₕ₂≤254 = ≤.begin
    suc (toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + unsigned (b ∷ bₜ₂))
      ≤.≡⟨ sym (+-suc (toℕ bₕ₂' * 256 ^ (1 + length bₜ₂)) _) ⟩
    toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + suc (unsigned (b ∷ bₜ₂))
      ≤.≤⟨ +-monoʳ-≤ (toℕ bₕ₂' * 256 ^ (1 + length bₜ₂)) (unsigned< (b ∷ bₜ₂)) ⟩
    toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + 256 ^ (1 + length bₜ₂)
      ≤.≤⟨ +-monoˡ-≤ (256 ^ (1 + length bₜ₂)) (*-monoˡ-≤ (256 ^ (1 + length bₜ₂))
             (≤.begin
               toℕ (Fin.fromℕ<{m = toℕ bₕ₂ - 128}{n = 256} bₕ₂∸128<256) ≤.≡⟨ Fin.toℕ-fromℕ< bₕ₂∸128<256 ⟩
               toℕ bₕ₂ - 128 ≤.≤⟨ ∸-monoˡ-≤ 128 bₕ₂≤254 ⟩
               126 ≤.∎)) ⟩
    126 * 256 ^ (1 + length bₜ₂) + 256 ^ (1 + length bₜ₂) ≤.≡⟨ +-comm (126 * 256 ^ (1 + length bₜ₂)) _ ⟩
    127 * 256 ^ (1 + length bₜ₂) ≤.≤⟨ m≤m+n (127 * 256 ^ (1 + length bₜ₂)) _ ⟩
    127 * 256 ^ (1 + length bₜ₂) + 128 * 256 ^ length bₜ₂ ≤.∎

  lem₂ : toℕ bₕ₂ ≡ 255 →    toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + unsigned (b ∷ bₜ₂)
                         < 127      * 256 ^ (1 + length bₜ₂) + 128 * 256 ^ length bₜ₂
  lem₂ bₕ₂≡255 = ≤.begin
    suc (toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + unsigned (b ∷ bₜ₂)) ≤.≡⟨ sym (+-suc (toℕ bₕ₂' * 256 ^ (1 + length bₜ₂)) _) ⟩
    toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + suc (unsigned (b ∷ bₜ₂)) ≤.≡⟨⟩
    toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + suc (toℕ b * 256 ^ length bₜ₂ + unsigned bₜ₂)
      ≤.≡⟨ cong ((toℕ bₕ₂' * 256 ^ (1 + length bₜ₂)) +_) (sym (+-suc _ (unsigned bₜ₂))) ⟩
    toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + (toℕ b * 256 ^ length bₜ₂ + suc (unsigned bₜ₂))
      ≤.≤⟨ +-monoʳ-≤ (toℕ bₕ₂' * 256 ^ (1 + length bₜ₂))
             (+-mono-≤ (*-monoˡ-≤ (256 ^ length bₜ₂) ([ (λ x → contradiction bₕ₂≡255 (Nat.<⇒≢ x)) , proj₂ ]′ mr₂₂)
             ) (unsigned< bₜ₂)) ⟩
    toℕ bₕ₂' * 256 ^ (1 + length bₜ₂) + (127 * 256 ^ length bₜ₂ + 256 ^ length bₜ₂)
      ≤.≤⟨ +-monoˡ-≤ ((127 * 256 ^ length bₜ₂ + 256 ^ length bₜ₂))
             (*-monoˡ-≤ (256 ^ (1 + length bₜ₂)) bₕ₂'≤127) ⟩
    127 * 256 ^ (1 + length bₜ₂) + (127 * 256 ^ length bₜ₂ + 256 ^ length bₜ₂)
      ≤.≡⟨ cong (127 * (256 ^ (1 + length bₜ₂)) +_) (+-comm (127 * 256 ^ length bₜ₂) _) ⟩
    127 * 256 ^ (1 + length bₜ₂) + 128 * 256 ^ length bₜ₂ ≤.∎

twosComplement-injective : (bs₁ bs₂ : List UInt8) → length bs₁ ≡ length bs₂ → twosComplement bs₁ ≡ twosComplement bs₂ → bs₁ ≡ bs₂
twosComplement-injective [] [] len≡ twos≡ = refl
twosComplement-injective (x₁ ∷ bs₁) (x₂ ∷ bs₂) len≡ twos≡
  with toℕ x₁ Nat.≤? 127 | toℕ x₂ Nat.≤? 127
twosComplement-injective (x₁ ∷ bs₁) (x₂ ∷ bs₂) len≡ twos≡ | no ¬x₁≤127 | no ¬x₂≤127 =
  cong₂ _∷_ lem₄ (∷-injectiveʳ lem₃)
  where
  open ≡-Reasoning
  module ≤ = ≤-Reasoning

  x₁∸128<256 = Nat.≤-trans (s≤s (m∸n≤m (toℕ x₁) 128)) (Fin.toℕ<n x₁)
  x₂∸128<256 = Nat.≤-trans (s≤s (m∸n≤m (toℕ x₂) 128)) (Fin.toℕ<n x₂)

  x₁' = Fin.fromℕ<{m = toℕ x₁ - 128}{n = 256} x₁∸128<256
  x₂' = Fin.fromℕ<{m = toℕ x₂ - 128}{n = 256} x₂∸128<256

  x₁'≤127 : toℕ x₁' ≤ 127
  x₁'≤127 = ≤.begin
    toℕ x₁' ≤.≡⟨⟩
    toℕ (Fin.fromℕ<{m = toℕ x₁ - 128}{n = 256} x₁∸128<256) ≤.≡⟨ Fin.toℕ-fromℕ< x₁∸128<256 ⟩
    toℕ x₁ - 128 ≤.≤⟨ ∸-monoˡ-≤ 128 (+-cancelˡ-≤ 1 (Fin.toℕ<n x₁)) ⟩
    127 ≤.∎

  x₂'≤127 : toℕ x₂' ≤ 127
  x₂'≤127 = ≤.begin
    toℕ x₂' ≤.≡⟨⟩
    toℕ (Fin.fromℕ<{m = toℕ x₂ - 128}{n = 256} x₂∸128<256) ≤.≡⟨ Fin.toℕ-fromℕ< x₂∸128<256 ⟩
    toℕ x₂ - 128 ≤.≤⟨ ∸-monoˡ-≤ 128 (+-cancelˡ-≤ 1 (Fin.toℕ<n x₂)) ⟩
    127 ≤.∎

  lem₀ = Lemmas.neg◃-injective twos≡

  lem₁ :   128 * 256 ^ length bs₁ - unsigned (x₁' ∷ bs₁)
         ≡ 128 * 256 ^ length bs₁ - unsigned (x₂' ∷ bs₂)
  lem₁ = subst₀ (λ x → 128 * 256 ^ length bs₁ - unsigned (x₁' ∷ bs₁) ≡ 128 * 256 ^ x - unsigned (x₂' ∷ bs₂)){x = length bs₂}{y = length bs₁} (sym (Nat.suc-injective len≡)) lem₀

  lem₂ = ∸-cancelˡ-≡{m = 128 * 256 ^ length bs₁}{n = unsigned (x₁' ∷ bs₁)}{o = unsigned (x₂' ∷ bs₂)}
           (<⇒≤ (unsigned-head< x₁' bs₁{128} (s≤s x₁'≤127)))
           (subst₀ (λ x → unsigned (x₂' ∷ bs₂) ≤ 128 * (256 ^ x)) (sym $ Nat.suc-injective len≡)
             (<⇒≤ (unsigned-head< x₂' bs₂{128} (s≤s x₂'≤127))))
           lem₁

  lem₃ = unsigned-injective (x₁' ∷ bs₁) (x₂' ∷ bs₂) len≡ lem₂

  lem₄ : x₁ ≡ x₂
  lem₄ =
    toℕ-injective
      (∸-cancelʳ-≡ {o = 128} (≰⇒> ¬x₁≤127) (≰⇒> ¬x₂≤127) (begin
        toℕ x₁ - 128 ≡⟨ sym (Fin.toℕ-fromℕ< x₁∸128<256) ⟩
        toℕ x₁' ≡⟨ cong Fin.toℕ (∷-injectiveˡ lem₃) ⟩
        toℕ x₂' ≡⟨ Fin.toℕ-fromℕ< x₂∸128<256 ⟩
        toℕ x₂ - 128 ∎))
twosComplement-injective (x₁ ∷ bs₁) (x₂ ∷ bs₂) len≡ twos≡ | no ¬x₁≤127 | yes x₂≤127 =
  contradiction {P = ℤ.-[1+ _ ] ≡ ℤ.+ _}
    (trans (sym (proj₂ (twosComplement<0 x₁ bs₁))) twos≡)
    λ ()
twosComplement-injective (x₁ ∷ bs₁) (x₂ ∷ bs₂) len≡ twos≡ | yes x₁≤127 | no ¬x₂≤127 =
  contradiction {P = ℤ.-[1+ _ ] ≡ ℤ.+ _}
    (trans (sym (proj₂ (twosComplement<0 x₂ bs₂))) (sym twos≡))
    λ ()
twosComplement-injective (x₁ ∷ bs₁) (x₂ ∷ bs₂) len≡ twos≡ | yes x₁≤127 | yes x₂≤127 =
  unsigned-injective (x₁ ∷ bs₁) (x₂ ∷ bs₂) len≡ (ℤ.+-injective twos≡)
  where
  import Data.Integer.Properties as ℤ

-- asciiNum
--------------------------------------------------

asciiNum₁-injective
  : ∀ b₁ b₂ → All (((toℕ '0') ≤_) ∘ toℕ) (b₁ ∷ [ b₂ ])
    → asciiNum₁ b₁ ≡ asciiNum₁ b₂
    → b₁ ≡ b₂
asciiNum₁-injective b₁ b₂ (p₁ ∷ p₂ ∷ []) ascii≡ =
  toℕ-injective (∸-cancelʳ-≡ p₁ p₂ ascii≡)

asciiNum< : ∀ bs → All (InRange '0' '9') bs → asciiNum bs < 10 ^ length bs
asciiNum< [] allIR = s≤s z≤n
asciiNum< (x ∷ bs) (px ∷ allIR) = ≤.begin-strict
  asciiNum (x ∷ bs) ≤.≡⟨⟩
  asciiNum₁ x * 10 ^ length bs + asciiNum bs ≤.≡⟨⟩
  (toℕ x - 48) * 10 ^ length bs + asciiNum bs
    ≤.<⟨ +-monoʳ-< ((toℕ x - 48) * 10 ^ length bs) (asciiNum< bs allIR) ⟩
  (toℕ x - 48) * 10 ^ length bs + 10 ^ length bs
    ≤.≤⟨ +-monoˡ-≤ (10 ^ length bs)
           (*-monoˡ-≤ (10 ^ length bs)
             (∸-monoˡ-≤ 48 (proj₂ px))) ⟩
  9 * 10 ^ length bs + 10 ^ length bs
    ≤.≡⟨ cong (_+ (10 ^ length bs)) -- {(10 - 1) * 10 ^ length bs}{10 * 10 ^ length bs - 1 * 10 ^ length bs}
           (begin
             (10 - 1) * 10 ^ length bs ≡⟨ *-distribʳ-∸ (10 ^ length bs) 10 1 ⟩
             10 ^ (1 + length bs) - 1 * 10 ^ length bs ≡⟨ cong ((10 ^ (1 + length bs)) ∸_) (*-identityˡ (10 ^ length bs)) ⟩
             10 ^ (1 + length bs) - 10 ^ length bs ∎)
    ⟩
  (10 ^ (1 + length bs) - 10 ^ length bs) + 10 ^ length bs
    ≤.≡⟨ m∸n+n≡m (Lemmas.^-monoʳ-≤ 10 (s≤s z≤n) (n≤1+n (length bs))) ⟩
  10 ^ (1 + length bs) ≤.∎
  where
  module ≤ = ≤-Reasoning
  open ≡-Reasoning

-- asciiNum and showFixed
--------------------------------------------------
asciiNum₁∘showFixed₁≗id : ∀ n → n < 10 → asciiNum₁ (proj₁ (showFixed₁ n)) ≡ n
asciiNum₁∘showFixed₁≗id n (s≤s n≤9) =
  let (b , ir) = showFixed₁ n in
  begin
    asciiNum₁ b ≡⟨⟩
    toℕ b - toℕ '0' ≡⟨⟩
    toℕ (Fin.inject≤ (Fin.raise (toℕ '0') (n mod 10)) pf) - toℕ '0'
      ≡⟨ cong (_∸ toℕ '0')
           (begin
             toℕ (Fin.inject≤ (Fin.raise (toℕ '0') (n mod 10)) pf) ≡⟨ toℕ-inject≤ _ pf ⟩
             toℕ (Fin.raise (toℕ '0') (n mod 10)) ≡⟨ toℕ-raise (toℕ '0') (n mod 10) ⟩
             toℕ '0' + toℕ (n mod 10) ∎) ⟩
    toℕ '0' + toℕ (n mod 10) - toℕ '0' ≡⟨ m+n∸m≡n (toℕ '0') (toℕ (n mod 10)) ⟩
    toℕ (n mod 10) ≡⟨⟩
    toℕ (Fin.fromℕ< (m%n<n n 9) ) ≡⟨ toℕ-fromℕ< (m%n<n n 9) ⟩
    n % 10 ≡⟨ m≤n⇒m%n≡m n≤9 ⟩
    n ∎
  where
  open ≡-Reasoning

  pf : 58 ≤ 256
  pf = toWitness{Q = _ Nat.≤? _} tt

showFixed₁∘asciiNum₁≗id : ∀ b → InRange '0' '9' b → proj₁ (showFixed₁ (asciiNum₁ b)) ≡ b
showFixed₁∘asciiNum₁≗id b ir = Fin.toℕ-injective
  (begin
    toℕ (proj₁ (showFixed₁ (asciiNum₁ b))) ≡⟨⟩
    toℕ (proj₁ (showFixed₁ (toℕ b - toℕ '0'))) ≡⟨⟩
    toℕ c‴ ≡⟨ Fin.toℕ-inject≤ c“ pf ⟩
    toℕ c“ ≡⟨ Fin.toℕ-raise (toℕ '0') c' ⟩
    toℕ '0' + toℕ c'
      ≡⟨ cong (toℕ '0' +_)
           (begin
             (toℕ (Fin.fromℕ< (m%n<n (toℕ b - toℕ '0') 9)) ≡⟨ Fin.toℕ-fromℕ< ((m%n<n (toℕ b - toℕ '0') 9)) ⟩
             (toℕ b - toℕ '0') % 10 ≡⟨ m≤n⇒m%n≡m b-0<10 ⟩
             toℕ b - toℕ '0' ∎)) ⟩
    toℕ '0' + (toℕ b - toℕ '0') ≡⟨ m+[n∸m]≡n (proj₁ ir) ⟩
    toℕ b ∎)
  where
  module ≤ = ≤-Reasoning
  open ≡-Reasoning
  pf : 57 < 256
  pf = toWitness{Q = _ Nat.≤? _} tt

  c = toℕ b - toℕ '0'
  c' = c mod 10
  c“ = Fin.raise (toℕ '0') c'
  c‴ = Fin.inject≤ c“ pf

  ir' : InRange '0' '9' c‴
  ir' = proj₂ (showFixed₁ c)

  b-0<10 : toℕ b - toℕ '0' ≤ 9
  b-0<10 = ≤.begin
    toℕ b - toℕ '0' ≤.≤⟨ ∸-monoˡ-≤ (toℕ '0') (proj₂ ir) ⟩
    9 ≤.∎

asciiNum∘showFixed≗id : ∀ w n → n < 10 ^ w → asciiNum (showFixed w n) ≡ n
asciiNum∘showFixed≗id zero .zero (s≤s z≤n) = refl
asciiNum∘showFixed≗id (suc w) n n<10^w =
  let
    (c₁ , ir) = showFixed₁ quotient
    (cs , len≡ , irs) = showFixed' w (toℕ remainder)
  in
  begin
    asciiNum (showFixed (suc w) n) ≡⟨⟩
    asciiNum (c₁ ∷ cs) ≡⟨⟩
    asciiNum₁ c₁ * 10 ^ length cs + asciiNum cs
      ≡⟨ cong₂ _+_
           (cong (λ x → asciiNum₁ c₁ * (10 ^ x)) len≡)
           (asciiNum∘showFixed≗id w (toℕ remainder) (toℕ<n _)) ⟩
    asciiNum₁ c₁ * 10 ^ w + toℕ remainder
      ≡⟨ cong (λ x → x * (10 ^ w) + toℕ remainder)
           (asciiNum₁∘showFixed₁≗id quotient q<10) ⟩
    quotient * 10 ^ w + toℕ remainder ≡⟨ +-comm _ (toℕ remainder) ⟩
    toℕ remainder + quotient * 10 ^ w ≡˘⟨ property ⟩
    n ∎
  where
  module ≤ = ≤-Reasoning
  open ≡-Reasoning

  pf : False (10 ^ w ≟ 0)
  pf = fromWitnessFalse (>⇒≢ (1≤10^n w))

  dm : DivMod n (10 ^ w)
  dm = (n divMod (10 ^ w)){pf}

  open DivMod dm

  q<10 : quotient < 10
  q<10 = *-cancelʳ-<{10 ^ w} quotient 10 (≤.begin-strict
    quotient * 10 ^ w ≤.≤⟨ m≤n+m _ _ ⟩
    toℕ remainder + quotient * 10 ^ w ≤.≡⟨ sym property ⟩
    n ≤.<⟨ n<10^w ⟩
    10 ^ (suc w) ≤.∎)

showFixed∘asciiNum≗id : ∀ bs → All (InRange '0' '9') bs → showFixed (length bs) (asciiNum bs) ≡ bs
showFixed∘asciiNum≗id [] irs = refl
showFixed∘asciiNum≗id (b ∷ bs) (ir ∷ irs) =
  showFixed (suc (length bs)) (asciiNum₁ b * 10 ^ length bs + asciiNum bs)
    ≡⟨ cong (showFixed (1 + length bs)) (+-comm (asciiNum₁ b * 10 ^ length bs) (asciiNum bs)) ⟩
  showFixed (suc (length bs)) (asciiNum bs + asciiNum₁ b * 10 ^ length bs) ≡⟨⟩
  proj₁ (showFixed₁ quotient) ∷ showFixed (length bs) (toℕ remainder)
    ≡⟨ cong₂ _∷_ b≡ ih ⟩
  b ∷ bs ∎
  where
  open ≡-Reasoning
  module ≤ = ≤-Reasoning

  pf = fromWitnessFalse (>⇒≢ (1≤10^n (length bs)))
  n = asciiNum bs + asciiNum₁ b * 10 ^ length bs

  open DivMod ((n divMod (10 ^ length bs)){pf})

  q≡ : quotient ≡ asciiNum₁ b
  q≡ = begin
    quotient
      ≡⟨ Lemmas.+-distrib-/-divMod (asciiNum bs) (asciiNum₁ b * 10 ^ length bs){10 ^ length bs}
           (≤.begin-strict
             (asciiNum bs % 10 ^ length bs + asciiNum₁ b * 10 ^ length bs % 10 ^ length bs
               ≤.≡⟨ cong₂ _+_{u = asciiNum₁ b * 10 ^ length bs % 10 ^ length bs}
                      (Lemmas.m≤n⇒m%n≡m-mod' (asciiNum< bs irs))
                      (Lemmas.m*n%n≡0-mod (asciiNum₁ b) (10 ^ length bs){pf}) ⟩
             asciiNum bs + 0 ≤.≡⟨ +-identityʳ (asciiNum bs) ⟩
             asciiNum bs ≤.<⟨ asciiNum< bs irs ⟩
             _ ≤.∎)) ⟩
    asciiNum bs / 10 ^ length bs + asciiNum₁ b * 10 ^ length bs / 10 ^ length bs
      ≡⟨ cong₂ _+_ {x = asciiNum bs / 10 ^ length bs}
           (m<n⇒m/n≡0 (asciiNum< bs irs))
           (m*n/n≡m (asciiNum₁ b) (10 ^ length bs)) ⟩
    asciiNum₁ b ∎

  b≡ : proj₁ (showFixed₁ quotient) ≡ b
  b≡ = begin
    proj₁ (showFixed₁ quotient) ≡⟨ cong (λ x → proj₁ (showFixed₁ x)) q≡ ⟩
    proj₁ (showFixed₁ (asciiNum₁ b)) ≡⟨ showFixed₁∘asciiNum₁≗id b ir ⟩
    b ∎

  ≡asciiNum : toℕ remainder ≡ asciiNum bs
  ≡asciiNum = begin
    toℕ remainder ≡⟨ cong Fin.toℕ (Lemmas.[m+kn]%n≡m%n-divMod (asciiNum bs) (asciiNum₁ b) (10 ^ length bs)) ⟩
    toℕ ((asciiNum bs mod 10 ^ length bs){pf}) ≡⟨ Lemmas.m≤n⇒m%n≡m-mod (asciiNum< bs irs) ⟩
    asciiNum bs ∎

  ih : showFixed (length bs) (toℕ remainder) ≡ bs
  ih = trans (cong (showFixed (length bs)) ≡asciiNum) (showFixed∘asciiNum≗id bs irs)

asciiNum-injective
  : (xs₁ xs₂ : List UInt8) → All (InRange '0' '9') xs₁ → All (InRange '0' '9') xs₂
    → length xs₁ ≡ length xs₂
    → asciiNum xs₁ ≡ asciiNum xs₂
    → xs₁ ≡ xs₂
asciiNum-injective xs₁ xs₂ ir₁ ir₂ len≡ ascii≡ = begin
  xs₁ ≡˘⟨ showFixed∘asciiNum≗id xs₁ ir₁ ⟩
  showFixed (length xs₁) (asciiNum xs₁)
    ≡⟨ cong₂ showFixed len≡ ascii≡ ⟩
  showFixed (length xs₂) (asciiNum xs₂)
    ≡⟨ showFixed∘asciiNum≗id xs₂ ir₂ ⟩
  xs₂ ∎
  where
  open ≡-Reasoning

