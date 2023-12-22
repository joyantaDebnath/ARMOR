import      Armor.Grammar.Definitions
import      Armor.Grammar.IList.TCB
import      Armor.Grammar.IList.Properties
import      Armor.Grammar.Properties
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser.Core
import      Armor.Grammar.Parser.Maximal
import      Armor.Grammar.Parser.WellFounded
open import Armor.Prelude
  renaming (Σ to Sigma)
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Armor.Grammar.IList.Parser (Σ : Set) where

open Armor.Grammar.Definitions          Σ
open Armor.Grammar.IList.TCB            Σ
open Armor.Grammar.IList.Properties     Σ
open Armor.Grammar.Properties           Σ
open Armor.Grammar.Parallel             Σ
open Armor.Grammar.Parser.Core          Σ
open Armor.Grammar.Parser.Maximal       Σ
open Armor.Grammar.Parser.WellFounded   Σ

module parseIList
  {M : Set → Set} ⦃ _ : Monad M ⦄
  (underflow : M (Level.Lift _ ⊤))
  (A : @0 List Σ → Set) (@0 ne : NonEmpty A) (@0 nn : NoSubstrings A)
  (p : Parser (M ∘ Dec) A) where

  open ≡-Reasoning
  open import Tactic.MonoidSolver using (solve ; solve-macro)

  here' = "parseIList"

  parseIListWF : ∀ n → ParserWF (M ∘ Dec) (ExactLength (IList A) n)
  runParser (parseIListWF zero) xs _ = 
    return (yes
      (success [] 0 refl (mk×ₚ nil (─ refl)) xs refl))
  runParser (parseIListWF n@(suc _)) xs (WellFounded.acc rs) = do
    yes (success pre₀ r₀ r₀≡ (mk×ₚ v₀ (─ r₀≤len)) suf₀ ps≡₀)
      ← runParser (parse≤ n p nn underflow) xs
      where no ¬parse → do
        return ∘ no $ λ where
          (success .(bs₁ ++ bs₂) read read≡ (mk×ₚ (cons (mkIListCons{bs₁}{bs₂} head₁ tail₁ refl)) (─ bsLen)) suffix ps≡) →
            contradiction
              (success bs₁ _ refl
                (mk×ₚ head₁
                  (─ (m+n≤o⇒m≤o _{length bs₂} (Lemmas.≡⇒≤ (trans (sym $ length-++ bs₁) bsLen)))))
                (bs₂ ++ suffix)
                (begin bs₁ ++ bs₂ ++ suffix ≡⟨ solve (++-monoid Σ) ⟩
                       (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡ ⟩
                        xs ∎))
              ¬parse
    case <-cmp r₀ n of λ where
      (tri> _ _  r₀>n) →
        contradiction (≤-trans (Lemmas.≡⇒≤ r₀≡) r₀≤len) (<⇒≱ r₀>n)
      (tri≈ _ r₀≡n _)  → do
        let
          l₁ : IList A pre₀
          l₁ = cons (mkIListCons v₀ nil (sym $ ++-identityʳ _))

          pre₀Len : Erased (length pre₀ ≡ n)
          pre₀Len = ─ (begin
            length pre₀ ≡⟨ sym r₀≡ ⟩
            r₀ ≡⟨ r₀≡n ⟩
            n ∎)
        return (yes
          (success pre₀ _ r₀≡ (mk×ₚ l₁ pre₀Len) suf₀ ps≡₀))
      (tri< r₀<n _ _)  → do
        let @0 suf₀<xs : length suf₀ < length xs
            suf₀<xs = subst (λ i → length suf₀ < length i) ps≡₀ (Lemmas.length-++-< pre₀ suf₀ (ne v₀))
        yes (success pre₁ r₁ r₁≡ (mk×ₚ v₁ (─ r₁≡len-pre₁)) suf₁ ps≡₁)
          ← runParser (parseIListWF (n ∸ r₀)) suf₀ (rs _ suf₀<xs)
          where no ¬parse → do
            return ∘ no $ λ where
              (success prefix read read≡ (mk×ₚ nil (─ ())) suffix ps≡)
              (success .(bs₁ ++ bs₂) read read≡ (mk×ₚ (cons (mkIListCons{bs₁}{bs₂} h t refl)) (─ bsLen)) suffix ps≡) → ‼
                let @0 xs≡ : pre₀ ++ suf₀ ≡ bs₁ ++ bs₂ ++ suffix
                    xs≡ = begin pre₀ ++ suf₀            ≡⟨ ps≡₀ ⟩
                                 xs                     ≡⟨ sym ps≡ ⟩
                                 (bs₁ ++ bs₂) ++ suffix ≡⟨ solve (++-monoid Σ) ⟩
                                 bs₁ ++ bs₂ ++ suffix   ∎

                    @0 pre₀≡bs₁ : pre₀ ≡ bs₁
                    pre₀≡bs₁ = nn xs≡ v₀ h
                in
                contradiction
                  (success bs₂ _ refl
                    (mk×ₚ t
                      (─ +-cancelˡ-≡ r₀
                         (begin (r₀ + length bs₂         ≡⟨ cong (_+ length bs₂) r₀≡ ⟩
                                length pre₀ + length bs₂ ≡⟨ cong (λ x → length x + length bs₂) pre₀≡bs₁ ⟩
                                length bs₁ + length bs₂  ≡⟨ sym (length-++ bs₁) ⟩
                                length (bs₁ ++ bs₂)      ≡⟨ bsLen ⟩
                                n                        ≡⟨ sym (+-identityʳ _) ⟩
                                n + 0                    ≡⟨ cong (n +_) (sym (n∸n≡0 r₀)) ⟩
                                n + (r₀ - r₀)            ≡⟨ sym (+-∸-assoc n {r₀} ≤-refl) ⟩
                                (n + r₀) - r₀            ≡⟨ cong (_∸ r₀) (+-comm n _) ⟩
                                (r₀ + n) - r₀            ≡⟨ +-∸-assoc r₀ {n} (<⇒≤ r₀<n) ⟩
                                r₀ + (n - r₀)            ∎))))
                    suffix
                    (++-cancelˡ bs₁ (trans (sym xs≡) (cong (_++ suf₀) pre₀≡bs₁))))
                  ¬parse
        return (yes
          (success (pre₀ ++ pre₁) (r₀ + r₁)
            (begin (r₀ + r₁                   ≡⟨ cong (_+ r₁) r₀≡ ⟩
                    length pre₀ + r₁          ≡⟨ cong (length pre₀ +_) r₁≡ ⟩
                    length pre₀ + length pre₁ ≡⟨ (sym $ length-++ pre₀) ⟩
                    length (pre₀ ++ pre₁)     ∎))
            (mk×ₚ (cons (mkIListCons v₀ v₁ refl))
              (─(begin (length (pre₀ ++ pre₁)     ≡⟨ length-++ pre₀ ⟩
                         length pre₀ + length pre₁ ≡⟨ cong (_+ _) (sym r₀≡) ⟩
                         r₀ + length pre₁          ≡⟨ cong (r₀ +_) r₁≡len-pre₁ ⟩
                         r₀ + (n - r₀)             ≡⟨ sym (+-∸-assoc r₀ (<⇒≤ r₀<n)) ⟩
                         r₀ + n - r₀               ≡⟨ cong (_∸ r₀) (+-comm r₀ n) ⟩
                         n + r₀ - r₀               ≡⟨ +-∸-assoc n {n = r₀} ≤-refl ⟩
                         n + (r₀ - r₀)             ≡⟨ cong (n +_) (n∸n≡0 r₀) ⟩
                         n + 0                     ≡⟨ +-identityʳ n ⟩
                         n                         ∎))))
            suf₁
            (begin ((pre₀ ++ pre₁) ++ suf₁  ≡⟨ solve (++-monoid Σ) ⟩
                    pre₀ ++ pre₁ ++ suf₁    ≡⟨ cong (pre₀ ++_) ps≡₁ ⟩
                    pre₀ ++ suf₀            ≡⟨ ps≡₀ ⟩
                    xs                      ∎))))

  parseIList : ∀ n → Parser (M ∘ Dec) (ExactLength (IList A) n)
  parseIList n = parseWF (parseIListWF n)

  parseIListNonEmpty : ∀ n → Parser (M ∘ Dec) (ExactLength (IListNonEmpty A) n)
  parseIListNonEmpty n =
    parseEquivalent{A = Σₚ (ExactLength (IList A) n) (λ _ xs → Erased (lengthIList (fstₚ xs) ≥ 1))}
      (Iso.symEquivalent (proj₁ Distribute.×ₚ-Σₚ-iso))
        (parseSigma' (Parallel.ExactLength.nosubstrings _) (λ x → erased? (_ ≥? 1))
        (λ where
          (mk×ₚ l₁ (─ sndₚ₁)) (mk×ₚ l₂ (─ sndₚ₂)) ≥1 →
            ─ subst (_≥ 1) (lengthIList≡ ne nn l₁ l₂) (Erased.x ≥1))
        (parseIList n))

open parseIList public using (parseIList ; parseIListNonEmpty)

module parseIListMax
  (underflow : Logging ⊤)
  (A : @0 List Σ → Set) (@0 ne : NonEmpty A) (@0 nn : NoSubstrings A)
  (p : Parser (Logging ∘ Dec) A) where

  open LogDec
  open import Data.Nat.Induction
    hiding (Acc)
  open ≡-Reasoning
  open import Tactic.MonoidSolver using (solve ; solve-macro)

  parseIListMax : MaximalParser (IList A)
  parseIListMax = mkMaximalParser (λ xs → help xs (<-wellFounded (length xs)))
    where
    help : ∀ xs → @0 Acc _<_ (length xs) → Sigma _ _
    help [] a =
      (mkLogged []
        (yes (success [] _ refl nil [] refl)))
      , λ where
        pre' suf' x x₁ → subst₀ (λ x → length x ≤ 0) (sym $ ++-conicalˡ pre' suf' x) z≤n
    help xs'@(x ∷ xs) (acc rs) =
      let p = runParser p xs'
      in
      case p of λ where
        (mkLogged log (no ¬p)) →
          (mkLogged log (yes (success [] _ refl nil xs' refl)))
          , λ where
            .[] suf' eq nil → z≤n
            pre' suf' eq (consIList{bs₁}{bs₂} head₁ tail₁ bs≡) →
              contradiction
                (success bs₁ _ refl head₁ (bs₂ ++ suf')
                  (begin (bs₁ ++ bs₂ ++ suf' ≡⟨ solve (++-monoid Σ) ⟩
                         (bs₁ ++ bs₂) ++ suf' ≡⟨ (sym $ cong (_++ suf') bs≡) ⟩
                         pre' ++ suf' ≡⟨ eq ⟩
                         xs' ∎)))
                ¬p
        (mkLogged log (yes (success prefix read read≡ value suffix ps≡))) →
          let s = help suffix
                    (rs (length suffix)
                      (≤-Reasoning.begin
                        suc (length suffix)
                          ≤-Reasoning.≤⟨
                            subst (length suffix <_) (length-++ prefix)
                            (Lemmas.length-++-< prefix suffix (ne value)) ⟩
                        length prefix + length suffix ≤-Reasoning.≡⟨ sym (length-++ prefix) ⟩
                        length (prefix ++ suffix) ≤-Reasoning.≡⟨ cong length ps≡ ⟩
                        length xs' ≤-Reasoning.∎))
          in
          case s of λ where
            (mkLogged log (no ¬s) , _) →
              contradiction (success [] _ refl nil suffix refl) ¬s
            (mkLogged log' (yes (success prefix' read' read≡' value' suffix' ps≡')) , max) →
              (mkLogged (log ++ log')
                (yes
                  (success (prefix ++ prefix') (read + read')
                    (begin (read + read' ≡⟨ cong₂ _+_ read≡ read≡' ⟩
                           length prefix + length prefix' ≡⟨ (sym $ length-++ prefix) ⟩
                           length (prefix ++ prefix') ∎))
                    (consIList value value' refl)
                    suffix'
                    (begin ((prefix ++ prefix') ++ suffix' ≡⟨ solve (++-monoid Σ) ⟩
                           prefix ++ (prefix' ++ suffix') ≡⟨ cong (prefix ++_) ps≡' ⟩
                           prefix ++ suffix ≡⟨ ps≡ ⟩
                           xs' ∎)))))
              , λ where
                .[] suf' eq nil → z≤n
                pre' suf' eq (consIList{bs₁}{bs₂} head₁ tail₁ bs≡₁) →
                  let bs≡' : Erased (bs₁ ++ bs₂ ++ suf' ≡ prefix ++ suffix)
                      bs≡' = ─ (begin
                        (bs₁ ++ bs₂ ++ suf' ≡⟨ solve (++-monoid Σ) ⟩
                        (bs₁ ++ bs₂) ++ suf' ≡⟨ cong (_++ suf') (sym bs≡₁) ⟩
                        pre' ++ suf' ≡⟨ eq ⟩
                        xs' ≡⟨ sym ps≡ ⟩
                        prefix ++ suffix ∎))

                      prefix≡ : Erased (bs₁ ≡ prefix)
                      prefix≡ = ─ nn (Erased.x bs≡') head₁ value

                      suffix≡ : Erased (bs₂ ++ suf' ≡ suffix)
                      suffix≡ = ─ (Lemmas.++-cancel≡ˡ _ _ (Erased.x prefix≡) (Erased.x bs≡'))
                  in
                  uneraseDec
                    (≤-Reasoning.begin
                      length pre' ≤-Reasoning.≡⟨ cong length bs≡₁ ⟩
                      length (bs₁ ++ bs₂) ≤-Reasoning.≡⟨ length-++ bs₁ ⟩
                      length bs₁ + length bs₂ ≤-Reasoning.≡⟨ cong (λ x → length x + length bs₂) (̂‼ prefix≡) ⟩
                      length prefix + length bs₂ ≤-Reasoning.≤⟨ +-monoʳ-≤ (length prefix) (length bs₂ ≤ read' ∋ max _ suf' (Erased.x suffix≡) tail₁) ⟩
                      length prefix + read' ≤-Reasoning.≡⟨ cong (_+ read') (sym read≡) ⟩
                      read + read' ≤-Reasoning.∎)
                    (_ ≤? _)

  parseIListLowerBounded : ∀ n → LogDec.MaximalParser (IListLowerBounded A n)
  parseIListLowerBounded n = LogDec.mkMaximalParser help
    where
    module ≤ = ≤-Reasoning

    help : ∀ xs → Sigma _ _
    help xs =
      case LogDec.runMaximalParser parseIListMax xs of λ where
        (mkLogged log (no ¬p) , tt) →
          contradiction (success [] _ refl nil xs refl) ¬p
        (mkLogged log (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁)) , max₁) →
          case n ≤? lengthIList v₁ of λ where
            (no  n≰v₁) →
              (mkLogged (log ++ ["parseIListLowerBounded: lower bound violated"])
                 (no λ where
                   (success prefix read read≡ (mk×ₚ v (─ vLen)) suffix ps≡) →
                     contradiction
                       (≤.begin n ≤.≤⟨ vLen ⟩
                                lengthIList v
                                  ≤.≤⟨ lengthIList≤ ne nn prefix pre₁ (trans ps≡ (sym ps≡₁))
                                         (≤-trans (max₁ prefix suffix ps≡ v) (Lemmas.≡⇒≤ r₁≡))
                                         v v₁ ⟩
                                lengthIList v₁ ≤.∎)
                       n≰v₁))
              , tt
            (yes n≤v₁) →
              (mkLogged log (yes (success pre₁ _ r₁≡ (mk×ₚ v₁ (─ n≤v₁)) suf₁ ps≡₁)))
              , λ where
                pre' suf' ps'≡ (mk×ₚ fstₚ₁ _) → max₁ _ _ ps'≡ fstₚ₁

module parseIListMaxNoOverlap
  (underflow : Logging (Level.Lift Level.zero ⊤))
  (A : @0 List Σ → Set) (@0 ne : NonEmpty A) (@0 noo : NoOverlap A A)
  (p : LogDec.MaximalParser A) where

  open import Data.Nat.Induction
    hiding (Acc)
  open ≡-Reasoning
  open import Tactic.MonoidSolver using (solve ; solve-macro)

  parseIListMax : LogDec.MaximalParser (IList A)
  parseIListMax = LogDec.mkMaximalParser (λ xs → help xs (<-wellFounded (length xs)))
    where
    help : ∀ xs → @0 Acc _<_ (length xs) → Sigma _ _
    help [] a =
      (mkLogged []
        (yes (success [] _ refl nil [] refl)))
      , λ where
        pre' suf' x x₁ → subst₀ (λ x → length x ≤ 0) (sym $ ++-conicalˡ pre' suf' x) z≤n
    help xs'@(x ∷ xs) (acc rs) =
      case LogDec.runMaximalParser p xs' ret (const _) of λ where
        (mkLogged log (no ¬p) , tt) →
          (mkLogged log (yes (success [] _ refl nil xs' refl)))
          , λ where
            .[] suf' eq nil → z≤n
            pre' suf' eq (consIList{bs₁}{bs₂} head₁ tail₁ bs≡) →
              contradiction
                (success bs₁ _ refl head₁ (bs₂ ++ suf')
                  (begin (bs₁ ++ bs₂ ++ suf' ≡⟨ solve (++-monoid Σ) ⟩
                         (bs₁ ++ bs₂) ++ suf' ≡⟨ (sym $ cong (_++ suf') bs≡) ⟩
                         pre' ++ suf' ≡⟨ eq ⟩
                         xs' ∎)))
                ¬p
        (mkLogged log (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁)) , max₁) →
          let @0 a' : Acc _<_ (length suf₁)
              a' = rs _ $ ≤-Reasoning.begin
                     1 + length suf₁
                       ≤-Reasoning.≤⟨
                         subst (length suf₁ <_) (length-++ pre₁)
                           (Lemmas.length-++-< pre₁ suf₁ (ne v₁))
                       ⟩
                     length pre₁ + length suf₁ ≤-Reasoning.≡⟨ sym (length-++ pre₁) ⟩
                     length (pre₁ ++ suf₁) ≤-Reasoning.≡⟨ cong length ps≡₁ ⟩
                     length xs' ≤-Reasoning.∎
          in
          case help suf₁ a' ret (const _) of λ where
            (mkLogged log (no ¬p) , snd) →
              contradiction (success [] _ refl nil suf₁ refl) ¬p
            (mkLogged log₁ (yes (success pre₂ r₂ r₂≡ v₂ suf₂ ps≡₂)) , max₂) →
              (mkLogged (log ++ log₁)
                (yes
                  (success (pre₁ ++ pre₂) (r₁ + r₂)
                    (r₁ + r₂ ≡⟨ cong₂ _+_ r₁≡ r₂≡ ⟩
                    length pre₁ + length pre₂ ≡⟨ sym (length-++ pre₁) ⟩
                    length (pre₁ ++ pre₂) ∎)
                    (consIList v₁ v₂ refl) suf₂
                    ((pre₁ ++ pre₂) ++ suf₂ ≡⟨ solve (++-monoid Σ) ⟩
                    pre₁ ++ pre₂ ++ suf₂ ≡⟨ cong (pre₁ ++_) ps≡₂ ⟩
                    pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                    xs' ∎))))
              , λ where
                .[] suf' ps≡' nil → z≤n
                pre' suf' ps≡' (consIList{bs₁} head₁ nil bs≡₁) →
                  uneraseDec
                    (≤-Reasoning.begin length pre' ≤-Reasoning.≡⟨ cong length bs≡₁ ⟩
                                      length (bs₁ ++ []) ≤-Reasoning.≡⟨ length-++ bs₁ ⟩
                                      length bs₁ + 0
                                        ≤-Reasoning.≤⟨
                                          +-mono-≤
                                            (max₁ _ suf'
                                              (bs₁ ++ suf' ≡⟨ solve (++-monoid Σ) ⟩
                                              (bs₁ ++ []) ++ suf' ≡⟨ (cong (_++ suf') ∘ sym $ bs≡₁) ⟩
                                              pre' ++ suf' ≡⟨ ps≡' ⟩
                                              xs' ∎)
                                              head₁)
                                            z≤n ⟩
                                      r₁ + r₂ ≤-Reasoning.∎)
                    (_ ≤? _)
                pre' suf' ps≡' (consIList{bs₁} head₁ (consIList{bs₂}{bs₃} head₂ tail₂ refl) bs≡₁) →
                  let xs≡ : Erased (bs₁ ++ bs₂ ++ bs₃ ++ suf' ≡ pre₁ ++ suf₁)
                      xs≡ = ─ (begin bs₁ ++ bs₂ ++ bs₃ ++ suf' ≡⟨ solve (++-monoid Σ) ⟩
                                     (bs₁ ++ bs₂ ++ bs₃) ++ suf' ≡⟨ cong (_++ suf') (sym bs≡₁) ⟩
                                     pre' ++ suf' ≡⟨ ps≡' ⟩
                                     xs' ≡⟨ sym ps≡₁ ⟩
                                     pre₁ ++ suf₁ ∎)

                      bs₁≤ : Erased (length bs₁ ≤ r₁)
                      bs₁≤ = ─ max₁ bs₁ (bs₂ ++ bs₃ ++ suf')
                                 (begin (_ ≡⟨ ¡ xs≡ ⟩
                                        pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                                        xs' ∎))
                                 head₁

                      pre₁≡ : Erased (pre₁ ≡ bs₁ ++ drop (length bs₁) pre₁)
                      pre₁≡ = ─ Lemmas.drop-length-≤ bs₁  (bs₂ ++ bs₃ ++ suf') _ _ (¡ xs≡) (≤-trans (¡ bs₁≤) (Lemmas.≡⇒≤ r₁≡))

                      bs₁≡ : Erased (pre₁ ≡ bs₁)
                      bs₁≡ = ─ (caseErased noo bs₁ (drop (length bs₁) pre₁) suf₁ bs₂ (bs₃ ++ suf')
                                  (++-cancelˡ bs₁ (begin
                                    (bs₁ ++ drop (length bs₁) pre₁ ++ suf₁ ≡⟨ solve (++-monoid Σ) ⟩
                                    (bs₁ ++ drop (length bs₁) pre₁) ++ suf₁ ≡⟨ (cong (_++ suf₁) ∘ sym $ ¡ pre₁≡) ⟩
                                    pre₁ ++ suf₁ ≡⟨ (sym $ ¡ xs≡) ⟩
                                    _ ∎)))
                                  (subst₀! A (¡ pre₁≡) v₁) head₁
                                ret (const _) of λ where
                        (inj₁ x) → ─ (begin pre₁ ≡⟨ ¡ pre₁≡ ⟩
                                            bs₁ ++ drop (length bs₁) pre₁ ≡⟨ cong (bs₁ ++_) x ⟩
                                            bs₁ ++ [] ≡⟨ ++-identityʳ bs₁ ⟩
                                            bs₁ ∎)
                        (inj₂ y) → contradiction head₂ y)

                      bs₂++bs₃≤ : Erased (length (bs₂ ++ bs₃) ≤ r₂)
                      bs₂++bs₃≤ = ─ max₂ (bs₂ ++ bs₃) suf'
                                      (++-cancelˡ bs₁ (begin
                                        (bs₁ ++ (bs₂ ++ bs₃) ++ suf' ≡⟨ solve (++-monoid Σ) ⟩
                                        bs₁ ++ bs₂ ++ bs₃ ++ suf' ≡⟨ ¡ xs≡ ⟩
                                        pre₁ ++ suf₁ ≡⟨ cong (_++ suf₁) (¡ bs₁≡) ⟩
                                        bs₁ ++ suf₁ ∎)))
                                      (consIList head₂ tail₂ refl)
                  in
                  uneraseDec
                    (≤-Reasoning.begin (length pre' ≤-Reasoning.≡⟨ cong length bs≡₁ ⟩
                                      length (bs₁ ++ bs₂ ++ bs₃) ≤-Reasoning.≡⟨ length-++ bs₁ ⟩
                                      length bs₁ + length (bs₂ ++ bs₃) ≤-Reasoning.≤⟨ +-monoˡ-≤ (length (bs₂ ++ bs₃)) (¡ bs₁≤) ⟩
                                      r₁ + length (bs₂ ++ bs₃) ≤-Reasoning.≤⟨ +-monoʳ-≤ r₁ (¡ bs₂++bs₃≤) ⟩
                                      r₁ + r₂ ≤-Reasoning.∎))
                    (_ ≤? _)
 
open parseIListMax public
  using (parseIListMax)
