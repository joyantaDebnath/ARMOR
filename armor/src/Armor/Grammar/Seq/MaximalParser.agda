import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq.Properties
import      Armor.Grammar.Seq.TCB
import      Armor.Grammar.Parser.Core
import      Armor.Grammar.Parser.Maximal
open import Armor.Prelude
  renaming (Σ to Sigma)
open import Data.Nat.Properties
open import Tactic.MonoidSolver
  using (solve ; solve-macro)

module Armor.Grammar.Seq.MaximalParser (Σ : Set) where

open Armor.Grammar.Definitions    Σ
open Armor.Grammar.Parser.Core    Σ
open Armor.Grammar.Parser.Maximal Σ
open Armor.Grammar.Seq.Properties Σ
open Armor.Grammar.Seq.TCB        Σ

open ≡-Reasoning
open LogDec

parse& : ∀ {A B : @0 List Σ → Set} → MaximalParser A → MaximalParser B → @0 NoOverlap A B
         → MaximalParser (&ₚ A B)
parse&{A} p₁ p₂ noo = mkMaximalParser help
  where
  help : ∀ xs → Sigma _ _
  help xs =
   case runMaximalParser p₁ xs ret (const _) of λ where
     (mkLogged log (no ¬p) , snd) →
       (mkLogged log (no (λ where
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
       case runMaximalParser p₂ suf₁ ret (const _) of λ where
         (mkLogged log₂ (no ¬p) , _) →
           (mkLogged (log₁ ++ log₂)
             (no λ where
               (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} v₁' v₂' refl) suffix ps≡) → ‼
                 let xs≡ : Erased (bs₁ ++ bs₂ ++ suffix ≡ pre₁ ++ suf₁)
                     xs≡ = ─ (begin (bs₁ ++ bs₂ ++ suffix ≡⟨ solve (++-monoid Σ) ⟩
                                    (bs₁ ++ bs₂) ++ suffix ≡⟨⟩
                                    prefix ++ suffix ≡⟨ ps≡ ⟩
                                    xs ≡⟨ sym ps≡₁ ⟩
                                    pre₁ ++ suf₁ ∎))

                     bs₁≤ : Erased (length bs₁ ≤ r₁)
                     bs₁≤ = ─ max₁ bs₁ (bs₂ ++ suffix) (trans (sym (++-assoc bs₁ bs₂ _)) ps≡) v₁'

                     pre₁≡ : Erased (pre₁ ≡ bs₁ ++ drop (length bs₁) pre₁)
                     pre₁≡ =
                       ─ Lemmas.drop-length-≤ bs₁ (bs₂ ++ suffix) _ suf₁
                           (¡ xs≡) (≤-trans (Erased.x bs₁≤) (Lemmas.≡⇒≤ r₁≡))
                 in
                 case noo bs₁ (drop (length bs₁) pre₁) suf₁ bs₂ suffix
                        (++-cancelˡ bs₁ ∘ begin_ $
                          bs₁ ++ drop (length bs₁) pre₁ ++ suf₁ ≡⟨ sym (++-assoc bs₁ _ suf₁) ⟩
                          (bs₁ ++ drop (length bs₁) pre₁) ++ suf₁ ≡⟨ cong (_++ suf₁) (sym $ ¡ pre₁≡) ⟩
                          pre₁ ++ suf₁ ≡⟨ (sym $ ¡ xs≡) ⟩
                          bs₁ ++ bs₂ ++ suffix ∎)
                        (subst₀! A (¡ pre₁≡) v₁) v₁' ret (const _) of λ where
                   (inj₁ x) →
                     let bs₁≡ : Erased (pre₁ ≡ bs₁)
                         bs₁≡ = ─ (begin (pre₁ ≡⟨ ¡ pre₁≡ ⟩
                                         bs₁ ++ drop (length bs₁) pre₁ ≡⟨ cong (bs₁ ++_) x ⟩
                                         bs₁ ++ [] ≡⟨ ++-identityʳ bs₁ ⟩
                                         bs₁ ∎))
                     in
                     contradiction
                       (success bs₂ _ refl v₂' suffix (Lemmas.++-cancel≡ˡ bs₁ pre₁ (sym $ ¡ bs₁≡) (¡ xs≡)))
                       ¬p
                   (inj₂ y) → contradiction v₂' y))
           , tt
         (mkLogged log₂ (yes (success pre₂ r₂ r₂≡ v₂ suf₂ ps≡₂)) , max₂) →
           (mkLogged (log₁ ++ log₂) (yes
             (success (pre₁ ++ pre₂) (r₁ + r₂)
               (begin (r₁ + r₂ ≡⟨ cong₂ _+_ r₁≡ r₂≡ ⟩
                      length pre₁ + length pre₂ ≡⟨ sym (length-++ pre₁) ⟩
                      length (pre₁ ++ pre₂) ∎))
               (mk&ₚ v₁ v₂ refl) suf₂
               (begin ((pre₁ ++ pre₂) ++ suf₂ ≡⟨ solve (++-monoid Σ) ⟩
                      pre₁ ++ pre₂ ++ suf₂ ≡⟨ cong (pre₁ ++_) ps≡₂ ⟩
                      pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                      xs ∎)))))
           , λ where
             pre' suf' ps≡' (mk&ₚ{bs₁}{bs₂} fstₚ₁ sndₚ₁ bs≡) →
               let
                   xs≡ : Erased (bs₁ ++ bs₂ ++ suf' ≡ pre₁ ++ suf₁)
                   xs≡ = ─ (begin (bs₁ ++ bs₂ ++ suf' ≡⟨ solve (++-monoid Σ) ⟩
                                  (bs₁ ++ bs₂) ++ suf' ≡⟨ cong (_++ suf') ∘ sym $ bs≡ ⟩
                                  pre' ++ suf' ≡⟨ ps≡' ⟩
                                  xs ≡⟨ sym ps≡₁ ⟩
                                  pre₁ ++ suf₁ ∎))

                   bs₁≤ : Erased (length bs₁ ≤ r₁)
                   bs₁≤ = ─ max₁ bs₁ (bs₂ ++ suf')
                            (trans (¡ xs≡) ps≡₁)
                            fstₚ₁

                   pre₁≡ : Erased (pre₁ ≡ bs₁ ++ drop (length bs₁) pre₁)
                   pre₁≡ =
                     ─ Lemmas.drop-length-≤ bs₁ (bs₂ ++ suf') _ suf₁
                         (¡ xs≡) (≤-trans (Erased.x bs₁≤) (Lemmas.≡⇒≤ r₁≡))
               in
               uneraseDec
                 (case
                   noo bs₁ (drop (length bs₁) pre₁) suf₁ bs₂ suf'
                     (++-cancelˡ bs₁ (begin
                       (bs₁ ++ drop (length bs₁) pre₁ ++ suf₁ ≡⟨ solve (++-monoid Σ) ⟩
                       (bs₁ ++ drop (length bs₁) pre₁) ++ suf₁ ≡⟨ (cong (_++ suf₁) ∘ sym $ ¡ pre₁≡) ⟩
                       pre₁ ++ suf₁ ≡⟨ sym (¡ xs≡) ⟩
                       bs₁ ++ bs₂ ++ suf' ∎)))
                     (subst₀! A (¡ pre₁≡) v₁) fstₚ₁
                   ret (const _) of λ where
                   (inj₁ ≡[]) →
                     let
                       bs₁≡ : Erased (pre₁ ≡ bs₁)
                       bs₁≡ = ─ (begin (pre₁ ≡⟨ ¡ pre₁≡ ⟩
                                       bs₁ ++ drop (length bs₁) pre₁ ≡⟨ cong (bs₁ ++_) ≡[] ⟩
                                       bs₁ ++ [] ≡⟨ ++-identityʳ bs₁ ⟩
                                       bs₁ ∎))

                       bs₂≤ : Erased (length bs₂ ≤ r₂)
                       bs₂≤ = ─ max₂ _ suf' (Lemmas.++-cancel≡ˡ bs₁ pre₁ (sym (¡ bs₁≡)) (¡ xs≡)) sndₚ₁
                     in
                     uneraseDec
                       (≤-Reasoning.begin
                         length pre' ≤-Reasoning.≡⟨ cong length bs≡ ⟩
                         length (bs₁ ++ bs₂) ≤-Reasoning.≡⟨ length-++ bs₁ ⟩
                         length bs₁ + length bs₂ ≤-Reasoning.≤⟨ +-mono-≤ (¡ bs₁≤) (¡ bs₂≤) ⟩
                         r₁ + r₂ ≤-Reasoning.∎)
                       (_ ≤? _)
                   (inj₂ ¬b) → contradiction sndₚ₁ ¬b)
                 (_ ≤? _)

parse&ᵈ : {A : @0 List Σ → Set} {B : {@0 bs : List Σ} → A bs → @0 List Σ → Set}
          → @0 NoSubstrings A → @0 Unambiguous A
          → Parser (Logging ∘ Dec) A
          → (∀ {@0 bs} → Singleton (length bs) → (a : A bs) → MaximalParser (B a))
          → MaximalParser (&ₚᵈ A B)
parse&ᵈ{A}{B} nn ua p₁ p₂ = mkMaximalParser help
  where
  module ≤ = ≤-Reasoning

  help : ∀ xs → Sigma _ _
  help xs =
    case runParser p₁ xs ret (const _) of λ where
      (mkLogged log (no ¬p)) →
        (mkLogged log (no (λ where
          (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} v₁ v₂ refl) suffix ps≡) →
            contradiction
              (success bs₁ _ refl v₁ (bs₂ ++ suffix)
                (begin bs₁ ++ bs₂ ++ suffix ≡⟨ solve (++-monoid Σ) ⟩
                       (bs₁ ++ bs₂) ++ suffix ≡⟨⟩
                       prefix ++ suffix ≡⟨ ps≡ ⟩
                       xs ∎))
              ¬p)))
        , tt
      (mkLogged log₁ (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁))) →
        case runMaximalParser (p₂ (singleton r₁ r₁≡) v₁) suf₁ ret (const _) of λ where
          (mkLogged log₂ (no ¬p) , max) →
              mkLogged (log₁ ++ log₂) (no λ where
                (success prefix read read≡ (mk&ₚ{bs₁'}{bs₂'} v₁' v₂' refl) suffix ps≡) →
                  let
                    xs≡ : Erased (pre₁ ++ suf₁ ≡ bs₁' ++ bs₂' ++ suffix)
                    xs≡ = ─ (begin
                      (pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩ 
                      xs ≡⟨ sym ps≡ ⟩
                      (bs₁' ++ bs₂') ++ suffix ≡⟨ solve (++-monoid Σ) ⟩
                      bs₁' ++ bs₂' ++ suffix ∎))

                    pre₁≡ : Erased (pre₁ ≡ bs₁')
                    pre₁≡ = ─ nn (¡ xs≡) v₁ v₁'

                    v₁≋ : _≋_{A = A} v₁ v₁'
                    v₁≋ = mk≋ (‼ (¡ pre₁≡)) (ua _ _)
                  in
                  case v₁≋ of λ where
                    ≋-refl →
                      contradiction (success bs₂' _ refl v₂' suffix (++-cancelˡ pre₁ (sym (¡ xs≡)))) ¬p)
            , tt
          (mkLogged log₂ (yes (success pre₂ r₂ r₂≡ v₂ suf₂ ps≡₂)) , max) →
              mkLogged (log₁ ++ log₂) (yes
                (success (pre₁ ++ pre₂) (r₁ + r₂)
                  (begin (r₁ + r₂ ≡⟨ cong₂ _+_ r₁≡ r₂≡ ⟩
                         length pre₁ + length pre₂ ≡⟨ sym (length-++ pre₁) ⟩
                         length (pre₁ ++ pre₂) ∎))
                  (mk&ₚ v₁ v₂ refl) suf₂
                  (begin (pre₁ ++ pre₂) ++ suf₂ ≡⟨ solve (++-monoid Σ) ⟩
                       pre₁ ++ pre₂ ++ suf₂ ≡⟨ cong (pre₁ ++_) ps≡₂ ⟩
                       pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                       xs ∎)))
            , λ where
              pre' suf' ps≡' (mk&ₚ{bs₁}{bs₂} fstₚ₁ sndₚ₁ bs≡) →
                let
                  xs≡ : Erased (bs₁ ++ bs₂ ++ suf' ≡ pre₁ ++ suf₁)
                  xs≡ = ─ (begin (bs₁ ++ bs₂ ++ suf' ≡⟨ solve (++-monoid Σ) ⟩
                                 (bs₁ ++ bs₂) ++ suf' ≡⟨ cong (_++ suf') ∘ sym $ bs≡ ⟩
                                 pre' ++ suf' ≡⟨ ps≡' ⟩
                                 xs ≡⟨ sym ps≡₁ ⟩
                                 pre₁ ++ suf₁ ∎))

                  bs₁≡ : Erased (bs₁ ≡ pre₁)
                  bs₁≡ = ─ (nn (¡ xs≡) fstₚ₁ v₁)

                  v₁≡ : Erased ((bs₁ , fstₚ₁) ≡ (pre₁ , v₁))
                  v₁≡ = case bs₁≡ ret (const _) of λ where
                    (─ refl) →
                      case (‼ ua v₁ fstₚ₁) ret (const _) of λ where
                        refl → ─ refl
                in
                uneraseDec
                  (≤.begin
                    length pre' ≤.≡⟨ cong length bs≡ ⟩
                    length (bs₁ ++ bs₂) ≤.≡⟨ length-++ bs₁ ⟩
                    length bs₁ + length bs₂ ≤.≡⟨ cong (_+ length bs₂) (cong length (¡ bs₁≡)) ⟩
                    length pre₁ + length bs₂ ≤.≡⟨ cong (_+ length bs₂) (sym r₁≡) ⟩
                    r₁ + length bs₂
                      ≤.≤⟨ +-monoʳ-≤ r₁
                             (max bs₂ suf'
                                (Lemmas.++-cancel≡ˡ bs₁ pre₁ (¡ bs₁≡) (¡ xs≡))
                                (subst₀! {A = Sigma (List Σ) (λ xs → A xs)} (λ p → B (proj₂ p) bs₂ ) (¡ v₁≡) sndₚ₁))
                      ⟩
                    r₁ + r₂ ≤.∎)
                  (_ ≤? _)
 

parse&₁ : ∀ {A B : @0 List Σ → Set} → Parser (Logging ∘ Dec) A → @0 NoSubstrings A → MaximalParser B → MaximalParser (&ₚ A B)
parse&₁{A}{B} p₁ nn p₂ = mkMaximalParser help
  where
  help : ∀ xs
         → Sigma (Logging ∘ Dec $ Success (&ₚ A B) xs)
                 (Lift (Success (&ₚ A B) xs) GreatestSuccess)
  help xs =
    case runParser p₁ xs of λ where
      (mkLogged l₁ (no ¬p)) →
        mkLogged l₁ (no λ where
          (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} v₁ v₂ refl) suffix ps≡) →
            contradiction (success bs₁ _ refl v₁ (bs₂ ++ suffix) (trans (sym $ ++-assoc bs₁ bs₂ suffix) ps≡)) ¬p)
        , tt
      (mkLogged l₁ (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁))) →
        case singleton (runParser (MaximalParser.parser{B} p₂) suf₁) refl of λ where
          (singleton (mkLogged l₂ (no ¬p)) p₂≡) →
            (mkLogged (l₁ ++ l₂) ∘ no $ λ where
              (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} v₁' v₂' refl) suffix ps≡') → ‼
                let @0 xs≡ : bs₁ ++ bs₂ ++ suffix ≡ pre₁ ++ suf₁
                    xs≡ = begin bs₁ ++ bs₂ ++ suffix ≡⟨ (sym $ ++-assoc bs₁ _ _) ⟩
                                (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡' ⟩
                                xs ≡⟨ sym ps≡₁ ⟩
                                pre₁ ++ suf₁ ∎

                    @0 bs₁≡ : bs₁ ≡ pre₁
                    bs₁≡ = nn xs≡ v₁' v₁
                in
                contradiction (success bs₂ _ refl v₂' suffix (Lemmas.++-cancel≡ˡ _ _ bs₁≡ xs≡)) ¬p)
            , tt  
          (singleton (mkLogged l₂ (yes (success pre₂ r₂ r₂≡ v₂ suf₂ ps≡₂))) p₂≡) →
            (mkLogged (l₁ ++ l₂) ∘ yes $
              success (pre₁ ++ pre₂) (r₁ + r₂)
                (begin (r₁ + r₂ ≡⟨ cong₂ _+_ r₁≡ r₂≡ ⟩
                       length pre₁ + length pre₂ ≡⟨ (sym $ length-++ pre₁) ⟩
                       length (pre₁ ++ pre₂) ∎))
                (mk&ₚ v₁ v₂ refl) suf₂
                (begin (pre₁ ++ pre₂) ++ suf₂ ≡⟨ ++-assoc pre₁ _ _ ⟩
                       pre₁ ++ (pre₂ ++ suf₂) ≡⟨ cong (pre₁ ++_) ps≡₂ ⟩
                       pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                       xs ∎))
            , λ where
                pre' suf' xs≡ (mk&ₚ{bs₁}{bs₂} fstₚ₁ sndₚ₁ bs≡) →
                  uneraseDec
                    (≤-Reasoning.begin
                      length pre' ≤-Reasoning.≡⟨ cong length bs≡ ⟩
                      length (bs₁ ++ bs₂) ≤-Reasoning.≡⟨ length-++ bs₁ ⟩
                      length bs₁ + length bs₂
                        ≤-Reasoning.≡⟨
                          cong (λ x → length x + length bs₂)
                            (nn (begin (bs₁ ++ bs₂ ++ suf' ≡⟨ sym (++-assoc bs₁ _ _) ⟩
                                       (bs₁ ++ bs₂) ++ suf' ≡⟨ cong (_++ suf') (sym bs≡) ⟩
                                       pre' ++ suf' ≡⟨ xs≡ ⟩
                                       xs ≡⟨ sym ps≡₁ ⟩
                                       pre₁ ++ suf₁ ∎))
                              fstₚ₁ v₁)
                        ⟩
                      length pre₁ + length bs₂ ≤-Reasoning.≡⟨ cong (_+ length bs₂) (sym r₁≡) ⟩
                      r₁ + length bs₂
                        ≤-Reasoning.≤⟨
                          +-monoʳ-≤ r₁
                            (subst₀ (Lift (Success _ _) GreatestSuccess)
                              (sym p₂≡)
                              (MaximalParser.max p₂ suf₁)
                              bs₂ suf'
                              (Lemmas.++-cancel≡ˡ bs₁ pre₁
                                ((nn (begin (bs₁ ++ bs₂ ++ suf' ≡⟨ sym (++-assoc bs₁ _ _) ⟩
                                       (bs₁ ++ bs₂) ++ suf' ≡⟨ cong (_++ suf') (sym bs≡) ⟩
                                       pre' ++ suf' ≡⟨ xs≡ ⟩
                                       xs ≡⟨ sym ps≡₁ ⟩
                                       pre₁ ++ suf₁ ∎))
                              fstₚ₁ v₁))
                                (begin (bs₁ ++ bs₂ ++ suf' ≡⟨ (sym $ ++-assoc bs₁ _ _) ⟩
                                       (bs₁ ++ bs₂) ++ suf' ≡⟨ cong (_++ suf') (sym bs≡) ⟩
                                       pre' ++ suf' ≡⟨ xs≡ ⟩
                                       xs ≡⟨ sym ps≡₁ ⟩
                                       pre₁ ++ suf₁ ∎)))
                              sndₚ₁)
                        ⟩
                      r₁ + r₂ ≤-Reasoning.∎)
                    (_ ≤? _)
