import      Armor.Grammar.Definitions
import      Armor.Grammar.Option.TCB
import      Armor.Grammar.Parser.Core
import      Armor.Grammar.Parser.Maximal
import      Armor.Grammar.Seq
open import Armor.Prelude
  renaming (Σ to Sigma)
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Grammar.Option.MaximalParser (Σ : Set) where

open Armor.Grammar.Definitions    Σ
open Armor.Grammar.Option.TCB     Σ
open Armor.Grammar.Parser.Core    Σ
open Armor.Grammar.Parser.Maximal Σ
open Armor.Grammar.Seq            Σ

open LogDec

parseMax : ∀ {A : @0 List Σ → Set} → MaximalParser A → MaximalParser (Option A)
parseMax p = mkMaximalParser help
  where
  help : ∀ xs → Sigma _ _
  help xs =
    case runMaximalParser p xs ret (const _) of λ where
      (mkLogged log (no ¬p) , snd) →
        (mkLogged log (yes (success [] _ refl none xs refl)))
        , λ where
          .[] suf' ps'≡ none → z≤n
          pre' suf' ps'≡ (some x) → contradiction (success pre' _ refl x suf' ps'≡) ¬p
      (mkLogged log (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁)) , max) →
        (mkLogged log (yes (success pre₁ _ r₁≡ (some v₁) suf₁ ps≡₁)))
        , λ where
          .[] suf' ps'≡ none → z≤n
          pre' suf' ps'≡ (some x) →
            max _ _ ps'≡ x

parse&o₂ : ∀ {A B : @0 List Σ → Set} → MaximalParser A → MaximalParser (Option B) → @0 NoOverlap A B
           → MaximalParser (&ₚ A (Option B))
parse&o₂{A}{B} pa pb noo = mkMaximalParser help
  where
  open ≡-Reasoning

  help : ∀ xs
         → Sigma (Logging ∘ Dec $ Success (&ₚ A (Option B)) xs)
                 (Lift _ _)
  help xs =
    case runMaximalParser pa xs ret (const _) of λ where
      (mkLogged log₁ (no ¬p) , max₁) →
        (mkLogged log₁ (no (λ where
          (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} v₁ v₂ refl) suffix ps≡) →
            contradiction
              (success bs₁ _ refl v₁ (bs₂ ++ suffix)
                (begin bs₁ ++ bs₂ ++ suffix ≡⟨ solve (++-monoid Σ) ⟩
                       (bs₁ ++ bs₂) ++ suffix ≡⟨⟩
                       prefix ++ suffix ≡⟨ ps≡ ⟩
                       xs ∎))
              ¬p)))
        , tt
      (mkLogged log₁ (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁)) , max₁) →
        case runMaximalParser pb suf₁ ret (const _) of λ where
          (mkLogged log₂ (no ¬p) , snd) →
            contradiction (success [] _ refl none suf₁ refl) ¬p
          (mkLogged log₂ (yes (success pre₂ r₂ r₂≡ v₂ suf₂ ps≡₂)) , max₂) →
            (mkLogged (log₁ ++ log₂)
              (yes (success (pre₁ ++ pre₂) (r₁ + r₂)
                     (begin (r₁ + r₂ ≡⟨ ‼ (cong₂ _+_ r₁≡ r₂≡) ⟩
                            length pre₁ + length pre₂ ≡⟨ sym (length-++ pre₁) ⟩
                            length (pre₁ ++ pre₂) ∎ ))
                     (mk&ₚ v₁ v₂ refl) suf₂
                     (begin ((pre₁ ++ pre₂) ++ suf₂ ≡⟨ solve (++-monoid Σ) ⟩
                            pre₁ ++ pre₂ ++ suf₂ ≡⟨ cong (pre₁ ++_) ps≡₂ ⟩
                            pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                            xs ∎)))))
            , λ where
              pre' suf' ps'≡ (mk&ₚ {bs₁} {.[]} fstₚ₁ none bs≡) →
                uneraseDec
                  (≤-Reasoning.begin length pre' ≤-Reasoning.≡⟨ ‼ cong length (trans bs≡ (++-identityʳ bs₁)) ⟩
                                    length bs₁ ≤-Reasoning.≤⟨ max₁ bs₁ suf' (trans (cong (_++ suf') (trans (sym (++-identityʳ bs₁)) (sym bs≡))) ps'≡) fstₚ₁  ⟩
                                    r₁ ≤-Reasoning.≤⟨ ≤-stepsʳ r₂ ≤-refl ⟩
                                    r₁ + r₂ ≤-Reasoning.∎)
                  (_ ≤? _)
              pre' suf' ps'≡ (mk&ₚ{bs₁}{bs₂} fstₚ₁ (some sndₚ₁) bs≡) →
                let xs≡ : Erased (bs₁ ++ bs₂ ++ suf' ≡ pre₁ ++ suf₁)
                    xs≡ = ─ (begin (bs₁ ++ bs₂ ++ suf' ≡⟨ solve (++-monoid Σ) ⟩
                                 (bs₁ ++ bs₂) ++ suf' ≡⟨ cong (_++ suf') (sym bs≡) ⟩
                                 pre' ++ suf' ≡⟨ ps'≡ ⟩
                                 xs ≡⟨ sym ps≡₁ ⟩
                                 pre₁ ++ suf₁ ∎))

                    bs₁≤ : Erased (length bs₁ ≤ r₁)
                    bs₁≤ = ─ max₁ _ (bs₂ ++ suf') (trans (Erased.x xs≡) ps≡₁) fstₚ₁

                    pre₁≡ : Erased (pre₁ ≡ bs₁ ++ drop (length bs₁) pre₁)
                    pre₁≡ =
                      ─ Lemmas.drop-length-≤
                          bs₁ (bs₂ ++ suf') _ suf₁ (Erased.x xs≡)
                          (≤-trans (Erased.x bs₁≤) (Lemmas.≡⇒≤ r₁≡))
                in
                uneraseDec
                  (case (noo bs₁ (drop (length bs₁) pre₁) suf₁ _ suf'
                          ((++-cancelˡ bs₁ (sym (begin
                            (bs₁ ++ bs₂ ++ suf' ≡⟨ Erased.x xs≡ ⟩ 
                            pre₁ ++ suf₁ ≡⟨ cong (_++ suf₁) (Erased.x pre₁≡) ⟩
                            (bs₁ ++ drop (length bs₁) pre₁) ++ suf₁ ≡⟨ ++-assoc bs₁ _ suf₁ ⟩
                            bs₁ ++ drop (length bs₁) pre₁ ++ suf₁ ∎)))))
                          (subst₀! A (Erased.x pre₁≡) v₁) fstₚ₁)
                   of λ where
                    (inj₁ ≡[]) →
                      let pre₁≡' : Erased (pre₁ ≡ bs₁)
                          pre₁≡' = ─ (begin (pre₁ ≡⟨ Erased.x pre₁≡ ⟩
                                            bs₁ ++ drop (length bs₁) pre₁ ≡⟨ cong (bs₁ ++_) ≡[] ⟩
                                            bs₁ ++ [] ≡⟨ ++-identityʳ bs₁ ⟩
                                            bs₁ ∎))
                          suf₁≡ : Erased (suf₁ ≡ bs₂ ++ suf')
                          suf₁≡ = ─ ++-cancelˡ pre₁ (begin
                                      (pre₁ ++ suf₁ ≡⟨ sym (Erased.x xs≡) ⟩
                                      bs₁ ++ bs₂ ++ suf' ≡⟨ cong (_++ bs₂ ++ suf') (sym (Erased.x pre₁≡')) ⟩
                                      pre₁ ++ bs₂ ++ suf' ∎))
                          bs₂≤ : Erased (length bs₂ ≤ r₂)
                          bs₂≤ = ─ max₂ _ _ (sym $ Erased.x suf₁≡) (some sndₚ₁)
                      in
                      uneraseDec
                        (≤-Reasoning.begin
                          (length pre' ≤-Reasoning.≡⟨ cong length bs≡ ⟩
                          length (bs₁ ++ bs₂) ≤-Reasoning.≡⟨ length-++ bs₁ ⟩
                          length bs₁ + length bs₂ ≤-Reasoning.≤⟨ +-mono-≤ (Erased.x bs₁≤) (Erased.x bs₂≤) ⟩
                          r₁ + r₂ ≤-Reasoning.∎))
                        (_ ≤? _)
                    (inj₂ x) → contradiction sndₚ₁ x)
                  (_ ≤? _)

