open import Armor.Arith
open import Armor.Binary.Bits.TCB
open import Armor.Prelude
open import Data.Fin.Properties as Fin
open import Data.Nat.Properties as Nat
  hiding (_≟_)
import      Data.Vec.Properties as Vec

module Armor.Binary.Bits.Properties where

toBinary-injective : ∀ {n} → (i₁ i₂ : Fin (2 ^ n)) → toBinary{n} i₁ ≡ toBinary{n} i₂ → i₁ ≡ i₂
toBinary-injective{n} i₁ i₂ i≡ =
  help{n} i₁ i₂ self self (Lemmas.Vec-reverse-injective _ _ i≡)
  where
  open ≡-Reasoning
  module ≤ = ≤-Reasoning

  help : ∀ {n} (i₁ i₂ : Fin (2 ^ n))
         → (n₁ : Singleton (toℕ i₁)) (n₂ : Singleton (toℕ i₂))
         → ToBinary.aux n (↑ n₁) ≡ ToBinary.aux n (↑ n₂)
         → i₁ ≡ i₂
  help {zero} Fin.zero Fin.zero n₁ n₂ toB≡ = refl
  help {suc n} i₁ i₂ (singleton n₁ n₁≡) (singleton n₂ n₂≡) toB≡ =
    toℕ-injective
      (begin
        (toℕ i₁ ≡⟨ ‼ sym n₁≡ ⟩
        n₁ ≡⟨ sym (divmod2-*2 n₁) ⟩
        toℕ (mod2 n₁) + 2 * (div2 n₁) ≡⟨ cong (_+ (2 * (div2 n₁))) (cong toℕ (Vec.∷-injectiveˡ toB≡)) ⟩
        toℕ (mod2 n₂) + 2 * (div2 n₁) ≡⟨ cong (toℕ (mod2 n₂) +_) (cong (2 *_) i₁'≡) ⟩
        toℕ (mod2 n₂) + 2 * (toℕ i₁') ≡⟨ cong (toℕ (mod2 n₂) +_) (cong ((2 *_) ∘ toℕ) ih) ⟩
        toℕ (mod2 n₂) + 2 * (toℕ i₂') ≡⟨ cong (toℕ (mod2 n₂) +_) (cong (2 *_) (sym i₂'≡)) ⟩
        toℕ (mod2 n₂) + 2 * (div2 n₂) ≡⟨ divmod2-*2 n₂ ⟩
        n₂ ≡⟨ ‼ n₂≡ ⟩
        toℕ i₂ ∎))
    where
    i₁'< : div2 n₁ < 2 ^ n
    i₁'< = divmod2-mono-<' n₁ (2 ^ n) (subst₀ (_< (2 ^ (1 + n))) (sym n₁≡) (Fin.toℕ<n i₁))

    i₁' : Fin (2 ^ n)
    i₁' = Fin.fromℕ< i₁'<

    i₁'≡ : div2 n₁ ≡ toℕ i₁'
    i₁'≡ = sym (toℕ-fromℕ< i₁'<)

    i₂'< : div2 n₂ < 2 ^ n
    i₂'< = divmod2-mono-<' n₂ (2 ^ n) (subst₀ ((_< (2 ^ (1 + n)))) (sym n₂≡) (Fin.toℕ<n i₂))

    i₂' : Fin (2 ^ n)
    i₂' = Fin.fromℕ< i₂'<

    i₂'≡ : div2 n₂ ≡ toℕ i₂'
    i₂'≡ = sym (toℕ-fromℕ< i₂'<)

    ih = help{n} i₁' i₂' (singleton (div2 n₁) i₁'≡) (singleton (div2 n₂) i₂'≡) (Vec.∷-injectiveʳ toB≡)

fromBinary∘toBinary : ∀ {n} → (i : Fin (2 ^ n)) → fromBinary (toBinary{n} i) ≡ i
fromBinary∘toBinary{n} i = begin
  fromBinary (toBinary{n} i) ≡⟨⟩
  FromBinary.aux (Vec.reverse (toBinary{n} i)) ≡⟨⟩
  FromBinary.aux (Vec.reverse (Vec.reverse (ToBinary.aux n (toℕ i))))
    ≡⟨ cong (FromBinary.aux{n}) (Lemmas.Vec-reverse-inverse (ToBinary.aux n (toℕ i))) ⟩
  FromBinary.aux (ToBinary.aux n (toℕ i)) ≡⟨ aux∘aux{n} i _ refl ⟩
  i ∎
  where
  open ≡-Reasoning
  module ≤ = ≤-Reasoning

  aux∘aux : ∀ {n} → (i : Fin (2 ^ n)) (i' : ℕ) → i' ≡ toℕ i → FromBinary.aux (ToBinary.aux n i') ≡ i
  aux∘aux {zero} Fin.zero i' i'≡ = refl
  aux∘aux n@{suc n'} i i' i'≡
    with divmod2 i' | inspect divmod2 i'
  ... | (q , #0) | [ insp ]R = toℕ-injective (begin
    toℕ (subst Fin (suc[pred[n]]≡n {2 ^ n} (2^n≢0 n)) _) ≡⟨ Lemmas.Fin-toℕ-subst (Fin.inject₁ (Fin.2* (FromBinary.aux (ToBinary.aux n' q)))) ⟩
    toℕ (Fin.inject₁ (Fin.2* (FromBinary.aux (ToBinary.aux n' q)))) ≡⟨ toℕ-inject₁ _ ⟩
    toℕ (Fin.2* (FromBinary.aux (ToBinary.aux n' q))) ≡⟨ Lemmas.Fin-toℕ-2* (FromBinary.aux (ToBinary.aux n' q)) ⟩
    2 * toℕ (FromBinary.aux (ToBinary.aux n' q)) ≡⟨ cong (λ x → 2 * toℕ x) (aux∘aux{n'} q' q q≡) ⟩
    2 * toℕ q' ≡⟨ cong (2 *_) (sym q≡) ⟩
    2 * q ≡⟨ 2*q≡ ⟩
    i' ≡⟨ i'≡ ⟩
    toℕ i ∎)
    where
    q≡div2 : q ≡ div2 i'
    q≡div2 = cong proj₁ (sym insp)

    #0≡mod2 : #0 ≡ mod2 i'
    #0≡mod2 = cong proj₂ (sym insp)

    q<2^n' : q < 2 ^ n'
    q<2^n' = ≤.begin
      suc q ≤.≡⟨ cong suc q≡div2 ⟩
      suc (div2 i') ≤.≤⟨ divmod2-mono-<' i' (2 ^ n') (subst (_< (2 ^ n)) (sym i'≡) (Fin.toℕ<n i)) ⟩
      2 ^ n' ≤.∎

    2*q≡ : 2 * q ≡ i'
    2*q≡ = begin
      0 + 2 * q ≡⟨ cong₂ _+_ (cong (toℕ {A = Bool}) #0≡mod2) (cong (2 *_) q≡div2) ⟩
      toℕ (mod2 i') + 2 * div2 i' ≡⟨ divmod2-*2 i' ⟩
      i' ∎

    q' : Fin (2 ^ n')
    q' = Fin.fromℕ< {m = q} q<2^n'

    q≡ : q ≡ toℕ q'
    q≡ = sym (Fin.toℕ-fromℕ< q<2^n')
    
  ... | (q , #1) | [ insp ]R = toℕ-injective (begin
    toℕ (subst Fin (suc[pred[n]]≡n {2 ^ n} (2^n≢0 n)) _) ≡⟨ Lemmas.Fin-toℕ-subst (Fin.fromℕ 1 Fin.+ (Fin.2* FromBinary.aux (ToBinary.aux n' q))) ⟩
    toℕ (Fin.fromℕ 1 Fin.+ (Fin.2* FromBinary.aux (ToBinary.aux n' q))) ≡⟨⟩
    1 + toℕ (Fin.2* FromBinary.aux (ToBinary.aux n' q))
      ≡⟨ cong (1 +_) (begin
        toℕ (Fin.2* FromBinary.aux (ToBinary.aux n' q))
          ≡⟨ Lemmas.Fin-toℕ-2* (FromBinary.aux (ToBinary.aux n' q)) ⟩
        2 * toℕ (FromBinary.aux (ToBinary.aux n' q)) ≡⟨ cong (λ x → 2 * toℕ x) (aux∘aux{n'} q' q q≡) ⟩
        2 * toℕ q' ≡⟨ cong (2 *_) (sym q≡) ⟩
        2 * q ∎) ⟩
    1 + 2 * q ≡⟨ 2*q≡ ⟩
    i' ≡⟨ i'≡ ⟩
    toℕ i ∎)
    where
    q≡div2 : q ≡ div2 i'
    q≡div2 = cong proj₁ (sym insp)

    #1≡mod2 : #1 ≡ mod2 i'
    #1≡mod2 = cong proj₂ (sym insp)

    q<2^n' : q < 2 ^ n'
    q<2^n' = ≤.begin
      suc q ≤.≡⟨ cong suc q≡div2 ⟩
      suc (div2 i') ≤.≤⟨ divmod2-mono-<' i' (2 ^ n') (subst (_< (2 ^ n)) (sym i'≡) (Fin.toℕ<n i)) ⟩
      2 ^ n' ≤.∎

    2*q≡ : 1 + 2 * q ≡ i'
    2*q≡ = begin
      1 + 2 * q ≡⟨ cong₂ _+_ (cong (toℕ {A = Bool}) #1≡mod2) (cong (2 *_) q≡div2) ⟩
      toℕ (mod2 i') + 2 * div2 i' ≡⟨ divmod2-*2 i' ⟩
      i' ∎

    q' : Fin (2 ^ n')
    q' = Fin.fromℕ< {m = q} q<2^n'

    q≡ : q ≡ toℕ q'
    q≡ = sym (Fin.toℕ-fromℕ< q<2^n')

toBinary∘fromBinary : ∀ {n} → (i : Binary n) → toBinary{n} (fromBinary i) ≡ i
toBinary∘fromBinary{n} i = begin
  toBinary{n} (FromBinary.aux (Vec.reverse i)) ≡⟨⟩
  Vec.reverse (ToBinary.aux n (toℕ (FromBinary.aux (Vec.reverse i))))
    ≡⟨ cong (Vec.reverse {A = Bool} {n}){x = ToBinary.aux n (toℕ (FromBinary.aux (Vec.reverse i)))}{y = Vec.reverse i}
         (aux∘aux (Vec.reverse i) _ refl) ⟩
  Vec.reverse (Vec.reverse i) ≡⟨ Lemmas.Vec-reverse-inverse i ⟩
  i ∎
  where
  open ≡-Reasoning

  aux∘aux : ∀ {n} → (i : Binary n) (i' : ℕ) → i' ≡ toℕ (FromBinary.aux i) → ToBinary.aux n i' ≡ i
  aux∘aux {.zero} [] i' i'≡ = refl
  aux∘aux {.(suc _)} (#0 ∷ i) i' i'≡
    with divmod2 i' | div2i≡
    where
    div2i≡ : divmod2 i' ≡ (toℕ (FromBinary.aux i) , #0)
    div2i≡ = begin
      divmod2 i'
        ≡⟨ cong divmod2 (begin
             i' ≡⟨ i'≡ ⟩
             toℕ (subst Fin _ (Fin.inject₁ (Fin.2* (FromBinary.aux i))))
               ≡⟨ Lemmas.Fin-toℕ-subst (Fin.inject₁ (Fin.2* (FromBinary.aux i))) ⟩
             toℕ (Fin.inject₁ (Fin.2* (FromBinary.aux i))) ≡⟨ Fin.toℕ-inject₁ _ ⟩
             toℕ (Fin.2* (FromBinary.aux i)) ≡⟨ Lemmas.Fin-toℕ-2* (FromBinary.aux i) ⟩
             2 * toℕ (FromBinary.aux i) ∎) ⟩
      divmod2 (2 * toℕ (FromBinary.aux i)) ≡⟨ divmod2-cancel₀ (toℕ (FromBinary.aux i)) ⟩
      (toℕ (FromBinary.aux i) , #0) ∎
  ... | _ | refl = cong (#0 Vec.∷_) (aux∘aux i _ refl)
  aux∘aux {.(suc _)} (#1 ∷ i) i' i'≡
    with divmod2 i' | div2i≡
    where
    div2i≡ : divmod2 i' ≡ (toℕ (FromBinary.aux i) , #1)
    div2i≡ = begin
      divmod2 i'
        ≡⟨ cong divmod2 (begin
             i' ≡⟨ i'≡ ⟩
             toℕ (subst Fin _ (Fin.fromℕ 1 Fin.+ Fin.2* (FromBinary.aux i))) ≡⟨ Lemmas.Fin-toℕ-subst (Fin.fromℕ 1 Fin.+ Fin.2* (FromBinary.aux i)) ⟩
             toℕ (Fin.fromℕ 1 Fin.+ Fin.2* (FromBinary.aux i)) ≡⟨⟩
             1 + toℕ (Fin.2* (FromBinary.aux i)) ≡⟨ cong (1 +_) (Lemmas.Fin-toℕ-2* (FromBinary.aux i)) ⟩
             1 + 2 * toℕ (FromBinary.aux i) ∎)
        ⟩
      divmod2 (1 + 2 * toℕ (FromBinary.aux i)) ≡⟨ divmod2-cancel₁ (toℕ (FromBinary.aux i)) ⟩
      (toℕ (FromBinary.aux i) , #1) ∎
  ... | _ | refl = cong (#1 Vec.∷_) (aux∘aux i _ refl)
