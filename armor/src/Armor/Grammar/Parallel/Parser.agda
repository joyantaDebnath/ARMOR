import      Armor.Grammar.Definitions.NoSubstrings
import      Armor.Grammar.Definitions.Unambiguous
import      Armor.Grammar.Parallel.Properties
import      Armor.Grammar.Parallel.TCB
import      Armor.Grammar.Parser.Core
open import Armor.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Armor.Grammar.Parallel.Parser (Σ : Set) where

open Armor.Grammar.Definitions.NoSubstrings Σ
open Armor.Grammar.Definitions.Unambiguous  Σ
open Armor.Grammar.Parallel.TCB Σ 
open Armor.Grammar.Parser.Core  Σ

open ≡-Reasoning

module _ {M : Set → Set} ⦃ _ : Monad M ⦄ where
  parseSigma'
    : ∀ {A : @0 List Σ → Set} {B : (@0 xs : List Σ) → A xs → Set}
      → @0 NoSubstrings A
      → (∀ {xs} → Decidable (B xs))
      → (∀ {@0 xs} → (a₁ a₂ : A xs) → B _ a₁ → B _ a₂)
      → Parser (M ∘ Dec) A
      → Parser (M ∘ Dec) (Σₚ A B)
  runParser (parseSigma'{A}{B} nn d i p) xs = do
    (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁)) ← runParser p xs
      where no ¬parse → do
        return ∘ no $ λ
          x → contradiction
                (mapSuccess (λ { (mk×ₚ z _) → z}) x)
                ¬parse
    let pre₁' = take r₁ xs
    let pre₁≡ : Erased (pre₁ ≡ pre₁')
        pre₁≡ = ─ subst (λ x → pre₁ ≡ take x xs) (sym r₁≡)
                    (subst (λ x → pre₁ ≡ take (length pre₁) x) ps≡₁
                      (sym (Lemmas.take-length-++ pre₁ _)))
    let v₁' = subst₀! A (Erased.x pre₁≡) v₁
    case d {pre₁'} v₁' ret _ of λ where
      (no ¬p) →
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ v p) suffix ps≡) → ‼
            let @0 pre≡ : prefix ≡ take r₁ xs
                pre≡ = trans (nn (trans₀ ps≡ (sym ps≡₁)) v v₁) (Erased.x pre₁≡)

                v₁' = (subst₀! A (Erased.x pre₁≡) v₁)

                p' : B pre₁' v₁'
                p' = i (subst₀! A pre≡ v) v₁'
                       (≡-elim (λ {p} eq → B p (subst₀! A eq v)) p pre≡)
            in
            contradiction p' ¬p
      (yes p) → do
        let p' : B pre₁ v₁
            p' = (case pre₁≡ ret (λ x → v₁' ≡ subst₀! A (Erased.x x) v₁ → B pre₁ v₁) of λ where
              (─ refl) → λ v₁≡ → subst₀ (B pre₁') v₁≡ p) refl
        return (yes
          (success pre₁ _ r₁≡ (mk×ₚ v₁ p') _ ps≡₁))

  parseSigma
    : ∀ {A B}
      → @0 NoSubstrings A → @0 Unambiguous A
      → Parser (M ∘ Dec) A
      → (∀ {@0 xs} → Decidable (B xs))
      → Parser (M ∘ Dec) (Σₚ A B)
  parseSigma{B = B} nn ua p d = parseSigma' nn d (λ {xs} a₁ a₂ b → subst₀ (B xs) (ua a₁ a₂) b) p

parseN : {M : Set → Set} ⦃ _ : Monad M ⦄ →
         (n : ℕ) → M (Level.Lift _ ⊤) → Parser (M ∘ Dec) (ExactLengthString n)
runParser (parseN zero _) xs =
  return (yes (success [] _ refl (mk×ₚ (singleton [] refl) (─ refl)) xs refl))
runParser (parseN (suc n) m) [] = do
  m
  return ∘ no $ λ where
    (success .bs read read≡ (mk×ₚ (singleton bs refl) (─ bsLen)) suffix ps≡) → ‼
      (0≢1+n $ begin
        length{A = Σ} [] ≡⟨ cong length (sym (‼ ps≡)) ⟩
        length (bs ++ suffix) ≡⟨ length-++ bs ⟩
        length bs + length suffix ≡⟨ cong (_+ length suffix) bsLen ⟩
        suc n + length suffix ∎)
  where open ≡-Reasoning
runParser (parseN (suc n) m) (x ∷ xs) = do
  yes (success .v₁ r₁ r₁≡ (mk×ₚ (singleton v₁ refl) (─ v₁Len)) suf₁ ps≡₁) ← runParser (parseN n m) xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success .(x ∷ bs) read read≡ (mk×ₚ (singleton (x ∷ bs) refl) (─ bsLen)) suffix ps≡) →
          contradiction
            (success bs _ refl (mk×ₚ (singleton bs refl) (─ cong pred bsLen)) suffix (∷-injectiveʳ ps≡))
            ¬parse        
  return (yes
    (success _ _ (cong suc r₁≡) (mk×ₚ (singleton (x ∷ v₁) refl) (─ cong suc v₁Len)) suf₁ (cong (x ∷_) ps≡₁)))

parseExactLength : {M : Set → Set} ⦃ _ : Monad M ⦄ →
                   {A : @0 List Σ → Set} → @0 NoSubstrings A →
                   M (Level.Lift _ ⊤) →
                   Parser (M ∘ Dec) A →
                   ∀ n → Parser (M ∘ Dec) (ExactLength A n)
runParser (parseExactLength nn m p n) xs = do
  yes (success pre₀ r₀ r₀≡ v₀ suf₀ ps≡₀) ← runParser p xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk×ₚ v vLen) suffix ps≡) →
          contradiction
            (success prefix _ read≡ v suffix ps≡)
            ¬parse
  case r₀ ≟ n of λ where
    (no  r₀≢) → do
      m
      return ∘ no $ λ where
        (success prefix read read≡ (mk×ₚ v (─ vLen)) suffix ps≡) → ‼
          let @0 pre₀≡ : pre₀ ≡ prefix
              pre₀≡ = nn (trans ps≡₀ (sym ps≡)) v₀ v
          in
          contradiction
            (begin (r₀           ≡⟨ r₀≡ ⟩
                   length pre₀   ≡⟨ cong length pre₀≡ ⟩
                   length prefix ≡⟨ vLen ⟩
                   n ∎))
            r₀≢
    (yes refl) →
      return (yes (success pre₀ _ r₀≡ (mk×ₚ v₀ (─ sym r₀≡)) suf₀ ps≡₀))
  where open ≡-Reasoning

parse≤ : ∀ {A : @0 List Σ → Set} {M : Set → Set} ⦃ _ : Monad M ⦄ (n : ℕ) →
  Parser (M ∘ Dec) A → @0 NoSubstrings A → M (Level.Lift _ ⊤) →
  Parser (M ∘ Dec) (Length≤ A n)
runParser (parse≤{A} n p nn m) xs = do
  (yes (success pre₀ r₀ r₀≡ v₀ suf₀ ps≡₀)) ← runParser p xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk×ₚ v _) suffix ps≡) →
          contradiction (success prefix _ read≡ v suffix ps≡) ¬parse
  case r₀ ≤? n of λ where
    (no  r₀≰n) → do
      m
      return ∘ no $ λ where
        (success prefix r r≡ (mk×ₚ v (─ r≤n)) suffix ps≡) →
          contradiction
            (≤.begin (r₀         ≤.≡⟨ r₀≡ ⟩
                   length pre₀   ≤.≡⟨ cong length (nn (trans ps≡₀ (sym ps≡)) v₀ v) ⟩
                   length prefix ≤.≤⟨ r≤n ⟩
                   n ≤.∎))
            r₀≰n
    (yes r₀≤n) →
      return (yes (success pre₀ _ r₀≡ (mk×ₚ v₀ (─ subst₀! (λ i → i ≤ n) r₀≡ r₀≤n)) suf₀ ps≡₀))
  where module ≤ = ≤-Reasoning

parse×Singleton
  : {M : Set → Set} ⦃ _ : Monad M ⦄ {A : @0 List Σ → Set}
    → Parser (M ∘ Dec) A
    → Parser (M ∘ Dec) (A ×ₚ Singleton)
runParser (parse×Singleton p) xs = do
  yes (success pre r r≡ v suf ps≡) ← runParser p xs
    where no ¬p → return ∘ no $ λ where
      (success pre r r≡ (mk×ₚ v _ ) suf ps≡) →
        contradiction (success pre _ r≡ v suf ps≡) ¬p
  return (yes (success
    pre r r≡
      (mk×ₚ v
        (singleton (take r xs)
          (begin take r xs ≡⟨ cong (take r) (sym ps≡) ⟩
                 take r (pre ++ suf) ≡⟨ cong (λ x → take x (pre ++ suf)) r≡ ⟩
                 take (length pre) (pre ++ suf) ≡⟨ Lemmas.take-length-++ pre suf ⟩
                 pre ∎))
        )
      suf ps≡))

parse×Dec : {M : Set → Set} ⦃ _ : Monad M ⦄ {A B : @0 List Σ → Set}
            → @0 NoSubstrings A
            → (decNo : M (Level.Lift _ ⊤))
            → Parser (M ∘ Dec) A → Decidable (λ xs → B xs)
            → Parser (M ∘ Dec) (A ×ₚ B)
runParser (parse×Dec{M}{A = A}{B} nn₁ decNo p b?) xs = do
  yes x ← runParser p xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk×ₚ value _ ) suffix ps≡) →
          contradiction (success prefix _ read≡ value suffix ps≡) ¬parse
  check x
  where
  check : Success A xs → M (Dec (Success (A ×ₚ B) xs))
  check (success prefix read read≡ value suffix ps≡) =
    case v₁ ret _ of λ where
      (no ¬b) → do
        decNo
        return ∘ no $ λ where
          (success prefix' read' read≡' (mk×ₚ v₀' b' ) suffix' ps≡') → ‼
            let @0 prefix≡ : prefix ≡ prefix'
                prefix≡ = nn₁ (trans₀ ps≡ (sym ps≡')) value v₀'
            in
            contradiction (subst₀! B (sym prefix≡) b') ¬b
      (yes b) → return (yes (success _ _ read≡ (mk×ₚ value b ) suffix ps≡))
    where
    v₁ : Dec (B prefix)
    v₁ = subst₀ (λ xs → Dec (B xs)) (take read xs ≡ prefix ∋ trans₀ (cong₂ take read≡ (sym ps≡)) (Lemmas.take-length-++ prefix suffix)) (b? (take read xs))

  -- case b? (take r₀ xs) of λ where
  --   x → {!!}

parse× : {M : Set → Set} ⦃ _ : Monad M ⦄ {A B : @0 List Σ → Set}
         → @0 NoSubstrings A → @0 NoSubstrings B
         → (mismatch : M (Level.Lift _ ⊤))
         → Parser (M ∘ Dec) A → Parser (M ∘ Dec) B
         → Parser (M ∘ Dec) (A ×ₚ B)
runParser (parse×{B = B} nn₁ nn₂ m p₁ p₂) xs = do
  yes (success pre₀ r₀ r₀≡ v₀ suf₀ ps≡₀) ← runParser p₁ xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk×ₚ v₀' v₁' ) suffix ps≡) →
          contradiction
            (success _ _ read≡ v₀' _ ps≡)
            ¬parse
  yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁) ← runParser p₂ xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk×ₚ v₀' v₁' ) suffix ps≡) →
          contradiction
            (success _ _ read≡ v₁' _ ps≡)
            ¬parse
  case r₀ ≟ r₁ of λ where
    (no  r₀≢r₁) → do
      m
      return ∘ no $ λ where
        (success prefix read read≡ (mk×ₚ v₀' v₁' ) suffix ps≡) → ‼
          contradiction
            (begin (r₀ ≡⟨ r₀≡ ⟩
                   length pre₀ ≡⟨ cong length (nn₁ (trans₀ ps≡₀ (sym ps≡)) v₀ v₀') ⟩
                   length prefix ≡⟨ cong length (nn₂ (trans₀ ps≡ (sym ps≡₁)) v₁' v₁) ⟩
                   length pre₁ ≡⟨ sym r₁≡ ⟩
                   r₁ ∎))
            r₀≢r₁
    (yes refl) →
      return (yes
        (success pre₀ r₀ r₀≡ (mk×ₚ v₀ (subst₀! B (proj₁ (Lemmas.length-++-≡ _ _ _ _ (trans ps≡₁ (sym ps≡₀)) (trans (sym r₁≡) r₀≡))) v₁) ) suf₀ ps≡₀))


