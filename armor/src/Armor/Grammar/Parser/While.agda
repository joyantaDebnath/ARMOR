import      Armor.Grammar.Definitions
import      Armor.Grammar.Parser.Core
open import Armor.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Armor.Grammar.Parser.While (Σ : Set) where

open Armor.Grammar.Definitions Σ
open Armor.Grammar.Parser.Core Σ

-- Parse while a given guard is true, but it *must* be terminated by a symbol
-- for which the guard is false (rather than from running out of symbols)
-- TODO: erasure for prefix, allPrefix should be flipped
-- TODO: either ¬term or EOF
record ParseWhileₜ (A : Σ → Set) (@0 xs : List Σ) : Set where
  constructor mkParseWhile
  field
    prefix : List Σ
    term   : Σ
    @0 allPrefix : All A prefix
    @0 ¬term     : ¬ A term
    @0 ps≡    : prefix ∷ʳ term ≡ xs


module Properties where
  private
    nosubstringsWF
      : ∀ {A : Σ → Set} {xs₁ ys₁ xs₂ ys₂}
        → Acc _<_ (length (xs₁ ++ ys₁))
        → (xs₁++ys₁≡xs₂++ys₂ : xs₁ ++ ys₁ ≡ xs₂ ++ ys₂)
        → (a₁ : ParseWhileₜ A xs₁) (a₂ : ParseWhileₜ A xs₂) → xs₁ ≡ xs₂
    nosubstringsWF (WellFounded.acc rs) xs₁++ys₁≡xs₂++ys₂ (mkParseWhile [] term allPrefix ¬term refl) (mkParseWhile [] term₁ allPrefix₁ ¬term₁ refl)
      = cong (_∷ []) (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂)
    nosubstringsWF (WellFounded.acc rs) xs₁++ys₁≡xs₂++ys₂ (mkParseWhile [] term allPrefix ¬term refl) (mkParseWhile (x ∷ prefix₁) term₁ allPrefix₁ ¬term₁ refl)
      = contradiction (subst _ (sym x≡) (All.head allPrefix₁)) ¬term
      where
      x≡ : term ≡ x
      x≡ = ∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂
    nosubstringsWF (WellFounded.acc rs) xs₁++ys₁≡xs₂++ys₂ (mkParseWhile (x ∷ prefix) term allPrefix ¬term refl) (mkParseWhile [] term₁ allPrefix₁ ¬term₁ refl)
      = contradiction (subst _ (sym x≡) (All.head allPrefix)) ¬term₁
      where
      x≡ : term₁ ≡ x
      x≡ = ∷-injectiveˡ (sym xs₁++ys₁≡xs₂++ys₂)
    nosubstringsWF (WellFounded.acc rs) xs₁++ys₁≡xs₂++ys₂ (mkParseWhile (x ∷ prefix) term allPrefix ¬term refl) (mkParseWhile (x₁ ∷ prefix₁) term₁ allPrefix₁ ¬term₁ refl)
      = cong₂ _∷_
          (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂)
          (nosubstringsWF (rs _ ≤-refl) (∷-injectiveʳ xs₁++ys₁≡xs₂++ys₂)
            (mkParseWhile prefix term (All.tail allPrefix) ¬term refl)
            (mkParseWhile prefix₁ term₁ (All.tail allPrefix₁) ¬term₁ refl))

  nosubstrings : ∀ {A} → NoSubstrings (ParseWhileₜ A)
  nosubstrings{xs₁ = xs₁}{ys₁} = nosubstringsWF (<-wellFounded (length (xs₁ ++ ys₁)))
    where open import Data.Nat.Induction

parseWhileₜ : ∀ {A : Σ → Set} (p : Decidable A) → Parser Dec (ParseWhileₜ A)
runParser (parseWhileₜ p) [] = no $ ‼ go
  where
  @0 go : ¬ Success (ParseWhileₜ _) []
  go (success .(prefix₁ ∷ʳ term) _ _ (mkParseWhile prefix₁ term allPrefix ¬term refl) suffix ps≡) =
    case [ term ] ≡ [] ∋ pf of λ ()
    where
    pf : [ term ] ≡ []
    pf = ++-conicalˡ [ term ] _ (++-conicalʳ prefix₁ _ (++-conicalˡ _ _ ps≡))
runParser (parseWhileₜ p) (x ∷ xs)
  with p x
... | no  pf = yes (success [ x ] _ refl (mkParseWhile [] x All.[] pf refl) xs refl)
... | yes a
  with runParser (parseWhileₜ p) xs
... | no  ¬parse = no $ ‼ go
  where
  @0 go : ¬ Success (ParseWhileₜ _) (x ∷ xs)
  go (success .([] ∷ʳ x) read read≡ (mkParseWhile [] .x allPrefix ¬term refl) suffix refl) =
    contradiction a ¬term
  go (success prefix₁@.((x ∷ xs₁) ∷ʳ term) read read≡ (mkParseWhile (x ∷ _) term (All._∷_ {xs = xs₁} px allPrefix) ¬term refl) suffix ps≡) =
    contradiction
      (success (xs₁ ∷ʳ term) _ refl
        (mkParseWhile xs₁ term allPrefix ¬term refl)
        suffix (∷-injectiveʳ ps≡))
      ¬parse
... | yes (success prefix read read≡ (mkParseWhile prefix₁ term allPrefix ¬term ps≡₁) suffix ps≡) =
  yes (success (x ∷ prefix) (1 + read) (cong suc read≡)
         (mkParseWhile (x ∷ prefix₁) term (a All.∷ allPrefix) ¬term (cong (x ∷_) ps≡₁))
         suffix (cong (x ∷_) ps≡))
