import      Armor.Grammar.Definitions
import      Armor.Grammar.Parser.Core
import      Armor.Grammar.Parser.Maximal
import      Armor.Grammar.Sum.TCB
open import Armor.Prelude
  renaming (Σ to Sigma)
import      Data.Nat.Properties as Nat

module Armor.Grammar.Sum.Parser (Σ : Set) where

open Armor.Grammar.Definitions    Σ
open Armor.Grammar.Parser.Core    Σ
open Armor.Grammar.Parser.Maximal Σ
open Armor.Grammar.Sum.TCB        Σ

module _ {M : Set → Set} ⦃ _ : Monad M ⦄ where
  parseSum : ∀ {A B : @0 List Σ → Set} → Parser (M ∘ Dec) A → Parser (M ∘ Dec) B → Parser (M ∘ Dec) (Sum A B)
  runParser (parseSum p₁ p₂) xs = do
    no ¬parse₁ ← runParser p₁ xs
      where yes x → return (yes (mapSuccess (λ {xs} x → Sum.inj₁ x) x))
    no ¬parse₂ ← runParser p₂ xs
      where yes x → return (yes (mapSuccess (λ {xs} x → Sum.inj₂ x) x))
    return ∘ no $ λ where
      (success prefix read read≡ (inj₁ x) suffix ps≡) →
        contradiction (success _ _ read≡ x suffix ps≡) ¬parse₁
      (success prefix read read≡ (inj₂ x) suffix ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬parse₂

parseMaxSum : ∀ {A B : @0 List Σ → Set}
              → LogDec.MaximalParser A
              → LogDec.MaximalParser B
              → LogDec.MaximalParser (Sum A B)
parseMaxSum p₁ p₂ = LogDec.mkMaximalParser help
  where
  open Nat.≤-Reasoning

  help : ∀ xs → Sigma _ _
  help xs =
    case (LogDec.runMaximalParser p₁ xs ,′e LogDec.runMaximalParser p₂ xs) ret (const _) of λ where
      ((mkLogged log (no ¬p) , _) , mkLogged log₁ (no ¬p₁) , _) →
        (mkLogged (log ++ log₁) (no (λ where
          (success prefix read read≡ (Sum.inj₁ x) suffix ps≡) →
            contradiction
              (success prefix _ read≡ x suffix ps≡)
              ¬p
          (success prefix read read≡ (Sum.inj₂ x) suffix ps≡) →
            contradiction
              (success prefix _ read≡ x suffix ps≡)
              ¬p₁)))
        , tt
      ((mkLogged log (no ¬p) , _) , mkLogged log₁ (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁)) , max₁) →
        (mkLogged (log ++ log₁) (yes (success pre₁ _ r₁≡ (Sum.inj₂ v₁) suf₁  ps≡₁)))
        , (λ where
          pre' suf' xs≡ (Sum.inj₁ x) → contradiction (success pre' _ refl x suf' xs≡) ¬p
          pre' suf' xs≡ (Sum.inj₂ x) → max₁ pre' suf' xs≡ x)
      ((mkLogged log (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁)) , max) , mkLogged log₁ (no ¬p₁) , _) →
        (mkLogged log (yes (success pre₁ r₁ r₁≡ (Sum.inj₁ v₁) _ ps≡₁)))
        , (λ where
          pre' suf' ps≡' (Sum.inj₁ x) → max pre' _ ps≡' x
          pre' suf' ps≡' (Sum.inj₂ x) → contradiction (success pre' _ refl x _ ps≡') ¬p₁)
      ((mkLogged log (yes (success pre r r≡ v suf ps≡)) , max) , mkLogged log₁ (yes (success pre₁ r₁ r≡₁ v₁ suf₁ ps≡₁)) , max₁) →
        case Nat.<-cmp r r₁ of λ where
          (tri< r<r₁ _ _) →
            (mkLogged (log ++ log₁) (yes (success pre₁ r₁ r≡₁ (Sum.inj₂ v₁) suf₁ ps≡₁)))
            , λ where
              pre' suf' ps≡' (Sum.inj₁ x) →
                begin (length pre' ≤⟨ max pre' _ ps≡' x ⟩
                      r ≤⟨ Nat.<⇒≤ r<r₁ ⟩
                      r₁ ∎)
              pre' suf' ps≡' (Sum.inj₂ x) → max₁ pre' _ ps≡' x
          (tri> _ _ r>r₁) →
            (mkLogged (log ++ log₁) (yes (success pre r r≡ (Sum.inj₁ v) suf ps≡)))
            , λ where
              pre' suf' ps≡' (Sum.inj₁ x) → max pre' _ ps≡' x
              pre' suf' ps≡' (Sum.inj₂ x) →
                begin (length pre' ≤⟨ max₁ pre' _ ps≡' x ⟩
                      r₁ ≤⟨ Nat.<⇒≤ r>r₁ ⟩
                      r ∎)
          (tri≈ _ refl _) →
            (mkLogged (log ++ log₁) (yes (success pre _ r≡ (Sum.inj₁ v) suf ps≡)))
            , λ where
              pre' suf' ps≡' (Sum.inj₁ x) →
                max pre' _ ps≡' x
              pre' suf' ps≡' (Sum.inj₂ x) →
                max₁ pre' _ ps≡' x
        
