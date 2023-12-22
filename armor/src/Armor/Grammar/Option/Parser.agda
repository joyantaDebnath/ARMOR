import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Option.Properties
import      Armor.Grammar.Option.TCB
import      Armor.Grammar.Parser
-- import      Armor.Grammar.Seq
open import Armor.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Grammar.Option.Parser (Σ : Set) where

open Armor.Grammar.Definitions       Σ
open Armor.Grammar.Option.Properties Σ
open Armor.Grammar.Option.TCB        Σ
open Armor.Grammar.Parallel          Σ
open Armor.Grammar.Parser            Σ
-- open Armor.Grammar.Seq               Σ

-- @0 prefixDecSuccess : ∀ {A xs} → Dec (Success A xs) → List Σ
-- prefixDecSuccess (no _) = []
-- prefixDecSuccess (yes (success prefix _ _ _ _ _ )) = prefix

-- readDecSuccess : ∀ {A xs} → Dec (Success A xs) → ℕ
-- readDecSuccess (yes s) = Success.read s
-- readDecSuccess (no  _) = 0

-- @0 read≡DecSuccess : ∀ {A xs} → (x : Dec (Success A xs)) → readDecSuccess x ≡ length (prefixDecSuccess x)
-- read≡DecSuccess (no _) = refl
-- read≡DecSuccess (yes (success prefix read read≡ _ _ _)) = read≡

-- valueDecSuccess : ∀ {A xs} → (x : Dec (Success A xs)) → Option A (prefixDecSuccess x)
-- valueDecSuccess (no _) = none
-- valueDecSuccess (yes (success prefix read read≡ value suffix ps≡)) = some value

-- suffixDecSuccess : ∀ {A xs} → Dec (Success A xs) → List Σ
-- suffixDecSuccess (yes s) = Success.suffix s
-- suffixDecSuccess{xs = xs} (no _) = xs

-- @0 ps≡DecSuccess : ∀ {A xs} → (x : Dec (Success A xs)) → prefixDecSuccess x ++ suffixDecSuccess x ≡ xs
-- ps≡DecSuccess (no _) = refl
-- ps≡DecSuccess (yes (success _ _ _ _ _ ps≡)) = ps≡

-- @0 yesPrefixDecSuccess : ∀ {A xs ys zs} → NoSubstrings A
--                          → (x : Dec (Success A xs)) → ys ++ zs ≡ xs → A ys → prefixDecSuccess x ≡ ys
-- yesPrefixDecSuccess nn (no ¬v) ++≡ v = ‼ (⊥-elim $ contradiction (success _ _ refl v _ ++≡) ¬v)
-- yesPrefixDecSuccess nn (yes (success prefix read read≡ value suffix ps≡)) ++≡ v =
--   ‼ nn (trans₀ ps≡ (sym ++≡)) value v

-- @0 noPrefixDecSuccess : ∀ {@0 A B xs ys zs} → NoConfusion A B
--                         → (x : Dec (Success A xs)) → ys ++ zs ≡ xs → B ys → prefixDecSuccess x ≡ []
-- noPrefixDecSuccess nc (no ¬parse) ++≡ v = refl
-- noPrefixDecSuccess nc (yes (success prefix read read≡ v' suffix ps≡)) ++≡ v =
--   ⊥-elim (contradiction v (nc (trans₀ ps≡ (sym ++≡)) v'))

-- ynPrefixDecSuccess : ∀ {@0 A B ws xs ys zs} → NoSubstrings A → NoConfusion A B
--                      → (x : Dec (Success A xs)) → ws ++ ys ++ zs ≡ xs → Option A ws → B ys → prefixDecSuccess x ≡ ws
-- ynPrefixDecSuccess{B = B}{ys = ys} nn nc (no _) ++≡  none v₂     = refl
-- ynPrefixDecSuccess{B = B}{ys = ys} nn nc (yes (success prefix read read≡ value suffix ps≡)) ++≡  none v₂     =
--   ‼ ⊥-elim (contradiction
--     v₂
--     (nc (trans₀ ps≡ (sym ++≡)) value))
-- ynPrefixDecSuccess nn nc (no ¬parse) ++≡ (some x₁) v₂ =
--   ‼ (⊥-elim (contradiction (success _ _ refl x₁ _ ++≡) ¬parse))
-- ynPrefixDecSuccess nn nc (yes (success prefix read read≡ value suffix ps≡)) ++≡ (some x₁) v₂ =
--   ‼ nn (trans₀ ps≡ (sym ++≡)) value x₁

-- -- ynPrefixDecSuccess nn nc (yes (success prefix read read≡ value suffix ps≡)) ++≡  none v₂ =
-- --   ‼ ⊥-elim (nc (trans₀ ps≡ (trans₀ (sym ++≡) (sym (++-identityʳ _)))) value v₂)
-- -- ynPrefixDecSuccess nn nc (yes (success prefix read read≡ value suffix ps≡)) ++≡ (some x) v₂ =
-- --   ‼ nn (trans₀ ps≡ (sym ++≡)) value x
-- -- ynPrefixDecSuccess nn nc (no ¬success) ++≡ v₁ v₂ = {!noPrefixDecSuccess nc !}

-- @0 noReadDecSuccess : ∀ {A B xs ys zs} → NoConfusion A B
--                         → (x : Dec (Success A xs)) → ys ++ zs ≡ xs → B ys → readDecSuccess x ≡ 0
-- noReadDecSuccess nc (no ¬parse) ++≡ v = refl
-- noReadDecSuccess nc (yes (success prefix read read≡ v' suffix ps≡)) ++≡ v =
--   ⊥-elim (contradiction v (nc (trans₀ ps≡ (sym ++≡)) v'))

-- @0 Length≤DecSuccess : ∀ {A xs n} → (x : Dec (Success (Length≤ A n) xs)) → readDecSuccess x ≤ n
-- Length≤DecSuccess (no _) = z≤n
-- Length≤DecSuccess {n = n} (yes (success prefix read read≡ (mk×ₚ fstₚ₁ (─ sndₚ₁)) suffix ps≡)) =
--   subst₀ (λ x → x ≤ n) (sym read≡) sndₚ₁

module _ {M : Set → Set} ⦃ _ : Monad M ⦄ where

  parseOption₁ExactLength
    : {A : @0 List Σ → Set}
      → @0 NoSubstrings A
      → (underflow : M (Level.Lift _ ⊤))
      → Parser (M ∘ Dec) A
      → ∀ n → Parser (M ∘ Dec) (ExactLength (Option A) n)
  runParser (parseOption₁ExactLength nn u p zero) xs =
    return (yes (success [] 0 refl (mk×ₚ none (─ refl)) xs refl))
  runParser (parseOption₁ExactLength  nn u p n'@(suc n)) xs = do
    yes (success pre₁ r₁ r₁≡ (mk×ₚ v₁ v₁Len) suf₁ ps≡₁) ← runParser (parseExactLength nn u p n') xs
      where no ¬parse → do
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ (some x) (─ v₁Len)) suffix ps≡) →
            contradiction
              (success prefix _ read≡ (mk×ₚ x (─ v₁Len)) suffix ps≡)
              ¬parse
    return (yes
      (success pre₁ _ r₁≡ (mk×ₚ (some v₁) v₁Len) suf₁ ps≡₁))


  open ≡-Reasoning

