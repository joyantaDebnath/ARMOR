import      Armor.Grammar.Definitions
import      Armor.Grammar.Parser.Core
open import Armor.Prelude
  renaming (Σ to Sigma)
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Grammar.Parser.Maximal
  (Σ : Set) where

open Armor.Grammar.Definitions          Σ
open Armor.Grammar.Parser.Core          Σ
  hiding (parseErased)

GreatestSuccess : ∀ {A xs} → Success A xs → Set
GreatestSuccess{A}{xs} s =
  ∀ pre' suf' → pre' ++ suf' ≡ xs → A pre'
  → length pre' ≤ Success.read s

module Generic (M : List Σ → Set → Set) (Lift : (A : Set) (P : A → Set) → (xs : List Σ) → M xs A → Set) where

  Maximal : ∀ {A} → Parserᵢ M A → Set
  Maximal{A} p = ∀ xs → Lift (Success A xs) GreatestSuccess xs (runParser p xs)

  record MaximalParser (A : @0 List Σ → Set) : Set where
    field
      parser : Parserᵢ M A
      max    : Maximal parser

  runMaximalParser : ∀ {A : @0 List Σ → Set} → (p : MaximalParser A) → ∀ xs → Sigma (M xs (Success A xs)) (Lift (Success A xs) GreatestSuccess xs)
  proj₁ (runMaximalParser p xs) = runParser (MaximalParser.parser p) xs
  proj₂ (runMaximalParser p xs) = MaximalParser.max p xs

module GenericSimple
  (M : Set → Set) (Lift : (A : Set) (P : A → Set) → M A → Set) where

  open Generic (const M) (λ A P _ → Lift A P) public

module LogDec where
  Lift : (A : Set) (P : A → Set) → Logging (Dec A) → Set
  Lift A P (mkLogged _ (no  _)) = ⊤
  Lift A P (mkLogged _ (yes x)) = P x

  open GenericSimple (Logging ∘ Dec) Lift public
  open ≡-Reasoning

  unlift : ∀ {A : @0 List Σ → Set} → (p : MaximalParser A)
           → ∀ xs {@0 pre} {suf} → pre ++ suf ≡ xs
           → A pre
           → Lift (Success A xs) GreatestSuccess (runParser (MaximalParser.parser p) xs)
           → Sigma (Success A xs) GreatestSuccess
  unlift p xs{pre}{suf} xs≡ a l
    with runParser (MaximalParser.parser p) xs
  ... | mkLogged log (no ¬p) = contradiction (success pre _ refl a suf xs≡) ¬p
  ... | mkLogged log (yes p₁) = p₁ , l

  mkMaximalParser
    : ∀ {@0 A}
      → (∀ xs → Sigma (Logging ∘ Dec $ Success A xs) (Lift (Success A xs) GreatestSuccess))
      → MaximalParser A
  runParser (MaximalParser.parser (mkMaximalParser {A} f)) xs =
    let (p , _) = f xs in p
  MaximalParser.max (mkMaximalParser {A} f) xs =
    let (_ , m) = f xs in m

  equivalent : ∀ {A B : @0 List Σ → Set} → Equivalent A B → MaximalParser A → MaximalParser B
  equivalent{A}{B} eq@(eq₁ , eq₂) p = mkMaximalParser help
    where
    help : ∀ xs → Sigma (Logging ∘ Dec $ Success B xs) (Lift (Success B xs) GreatestSuccess)
    help xs =
      case (_,e_{B = Lift (Success A xs) GreatestSuccess}
              (runParser (MaximalParser.parser p) xs)
              (MaximalParser.max p xs))
      ret (const _) of λ where
        (mkLogged l₁ (no ¬p) , _) →
          (mkLogged l₁ (no (contraposition (mapSuccess eq₂) ¬p))) ,e tt
        (mkLogged l₁ (yes s@(success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁)) , m) →
          (mkLogged l₁ (yes (mapSuccess eq₁ s))) ,e λ where
            pre' suf' xs≡ b → m pre' suf' xs≡ (eq₂ b)

  nonnesting : ∀ {A : @0 List Σ → Set} → @0 NoSubstrings A → Parser (Logging ∘ Dec) A → MaximalParser A
  MaximalParser.parser (nonnesting nn p) = p
  MaximalParser.max (nonnesting{A} nn p) xs =
    case runParser p xs ret (Lift _ _) of λ where
      (mkLogged log (no ¬p)) → tt
      (mkLogged log (yes p₁)) → help p₁
    where
    module _ (p₁ : Success A xs) where
      help : (pre' suf' : List Σ) → pre' ++ suf' ≡ xs → A pre' → length pre' ≤ Success.read p₁
      help pre' suf' eq a =
        Lemmas.≡⇒≤
          (trans₀
            (‼ cong length
              (nn (trans eq (sym (Success.ps≡ p₁))) a (Success.value p₁)))
            (sym $ Success.read≡ p₁))

  -- parse& : ∀ {@0 A B} → MaximalParser A → MaximalParser B → @0 NoOverlap A B
  --          → MaximalParser (&ₚ A B)
  -- parse&{A} p₁ p₂ noo = mkMaximalParser help
  --   where
  --   help : ∀ xs → Sigma _ _
  --   help xs =
  --     case runMaximalParser p₁ xs ret (const _) of λ where
  --       (mkLogged log (no ¬p) , snd) →
  --         (mkLogged log (no (λ where
  --           (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} v₁ v₂ refl) suffix ps≡) →
  --             contradiction
  --               (success bs₁ _ refl v₁ (bs₂ ++ suffix)
  --                 (begin bs₁ ++ bs₂ ++ suffix ≡⟨ solve (++-monoid Σ) ⟩
  --                        (bs₁ ++ bs₂) ++ suffix ≡⟨⟩
  --                        prefix ++ suffix ≡⟨ ps≡ ⟩
  --                        xs ∎))
  --               ¬p)))
  --         , tt
  --       (mkLogged log₁ (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁)) , max₁) →
  --         case runMaximalParser p₂ suf₁ ret (const _) of λ where
  --           (mkLogged log₂ (no ¬p) , _) →
  --             (mkLogged (log₁ ++ log₂)
  --               (no λ where
  --                 (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} v₁' v₂' refl) suffix ps≡) → ‼
  --                   let xs≡ : Erased (bs₁ ++ bs₂ ++ suffix ≡ pre₁ ++ suf₁)
  --                       xs≡ = ─ (begin (bs₁ ++ bs₂ ++ suffix ≡⟨ solve (++-monoid Σ) ⟩
  --                                      (bs₁ ++ bs₂) ++ suffix ≡⟨⟩
  --                                      prefix ++ suffix ≡⟨ ps≡ ⟩
  --                                      xs ≡⟨ sym ps≡₁ ⟩
  --                                      pre₁ ++ suf₁ ∎))

  --                       bs₁≤ : Erased (length bs₁ ≤ r₁)
  --                       bs₁≤ = ─ max₁ bs₁ (bs₂ ++ suffix) (trans (sym (++-assoc bs₁ bs₂ _)) ps≡) v₁'

  --                       pre₁≡ : Erased (pre₁ ≡ bs₁ ++ drop (length bs₁) pre₁)
  --                       pre₁≡ =
  --                         ─ Lemmas.drop-length-≤ bs₁ (bs₂ ++ suffix) _ suf₁
  --                             (¡ xs≡) (≤-trans (Erased.x bs₁≤) (Lemmas.≡⇒≤ r₁≡))
  --                   in
  --                   case noo bs₁ (drop (length bs₁) pre₁) suf₁ bs₂ suffix
  --                          (++-cancelˡ bs₁ ∘ begin_ $
  --                            bs₁ ++ drop (length bs₁) pre₁ ++ suf₁ ≡⟨ sym (++-assoc bs₁ _ suf₁) ⟩
  --                            (bs₁ ++ drop (length bs₁) pre₁) ++ suf₁ ≡⟨ cong (_++ suf₁) (sym $ ¡ pre₁≡) ⟩
  --                            pre₁ ++ suf₁ ≡⟨ (sym $ ¡ xs≡) ⟩
  --                            bs₁ ++ bs₂ ++ suffix ∎)
  --                          (subst A (¡ pre₁≡) v₁) v₁' ret (const _) of λ where
  --                     (inj₁ x) →
  --                       let bs₁≡ : Erased (pre₁ ≡ bs₁)
  --                           bs₁≡ = ─ (begin (pre₁ ≡⟨ ¡ pre₁≡ ⟩
  --                                           bs₁ ++ drop (length bs₁) pre₁ ≡⟨ cong (bs₁ ++_) x ⟩
  --                                           bs₁ ++ [] ≡⟨ ++-identityʳ bs₁ ⟩
  --                                           bs₁ ∎))
  --                       in
  --                       contradiction
  --                         (success bs₂ _ refl v₂' suffix (Lemmas.++-cancel≡ˡ bs₁ pre₁ (sym $ ¡ bs₁≡) (¡ xs≡)))
  --                         ¬p
  --                     (inj₂ y) → contradiction v₂' y))
  --             , tt
  --           (mkLogged log₂ (yes (success pre₂ r₂ r₂≡ v₂ suf₂ ps≡₂)) , max₂) →
  --             (mkLogged (log₁ ++ log₂) (yes
  --               (success (pre₁ ++ pre₂) (r₁ + r₂)
  --                 (begin (r₁ + r₂ ≡⟨ cong₂ _+_ r₁≡ r₂≡ ⟩
  --                        length pre₁ + length pre₂ ≡⟨ sym (length-++ pre₁) ⟩
  --                        length (pre₁ ++ pre₂) ∎))
  --                 (mk&ₚ v₁ v₂ refl) suf₂
  --                 (begin ((pre₁ ++ pre₂) ++ suf₂ ≡⟨ solve (++-monoid Σ) ⟩
  --                        pre₁ ++ pre₂ ++ suf₂ ≡⟨ cong (pre₁ ++_) ps≡₂ ⟩
  --                        pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
  --                        xs ∎)))))
  --             , λ where
  --               pre' suf' ps≡' (mk&ₚ{bs₁}{bs₂} fstₚ₁ sndₚ₁ bs≡) →
  --                 let
  --                     xs≡ : Erased (bs₁ ++ bs₂ ++ suf' ≡ pre₁ ++ suf₁)
  --                     xs≡ = ─ (begin (bs₁ ++ bs₂ ++ suf' ≡⟨ solve (++-monoid Σ) ⟩
  --                                    (bs₁ ++ bs₂) ++ suf' ≡⟨ cong (_++ suf') ∘ sym $ bs≡ ⟩
  --                                    pre' ++ suf' ≡⟨ ps≡' ⟩
  --                                    xs ≡⟨ sym ps≡₁ ⟩
  --                                    pre₁ ++ suf₁ ∎))

  --                     bs₁≤ : Erased (length bs₁ ≤ r₁)
  --                     bs₁≤ = ─ max₁ bs₁ (bs₂ ++ suf')
  --                              (trans (¡ xs≡) ps≡₁)
  --                              fstₚ₁

  --                     pre₁≡ : Erased (pre₁ ≡ bs₁ ++ drop (length bs₁) pre₁)
  --                     pre₁≡ =
  --                       ─ Lemmas.drop-length-≤ bs₁ (bs₂ ++ suf') _ suf₁
  --                           (¡ xs≡) (≤-trans (Erased.x bs₁≤) (Lemmas.≡⇒≤ r₁≡))
  --                 in
  --                 uneraseDec
  --                   (case
  --                     noo bs₁ (drop (length bs₁) pre₁) suf₁ bs₂ suf'
  --                       (++-cancelˡ bs₁ (begin
  --                         (bs₁ ++ drop (length bs₁) pre₁ ++ suf₁ ≡⟨ solve (++-monoid Σ) ⟩
  --                         (bs₁ ++ drop (length bs₁) pre₁) ++ suf₁ ≡⟨ (cong (_++ suf₁) ∘ sym $ ¡ pre₁≡) ⟩
  --                         pre₁ ++ suf₁ ≡⟨ sym (¡ xs≡) ⟩
  --                         bs₁ ++ bs₂ ++ suf' ∎)))
  --                       (subst A (¡ pre₁≡) v₁) fstₚ₁
  --                     ret (const _) of λ where
  --                     (inj₁ ≡[]) →
  --                       let
  --                         bs₁≡ : Erased (pre₁ ≡ bs₁)
  --                         bs₁≡ = ─ (begin (pre₁ ≡⟨ ¡ pre₁≡ ⟩
  --                                         bs₁ ++ drop (length bs₁) pre₁ ≡⟨ cong (bs₁ ++_) ≡[] ⟩
  --                                         bs₁ ++ [] ≡⟨ ++-identityʳ bs₁ ⟩
  --                                         bs₁ ∎))

  --                         bs₂≤ : Erased (length bs₂ ≤ r₂)
  --                         bs₂≤ = ─ max₂ _ suf' (Lemmas.++-cancel≡ˡ bs₁ pre₁ (sym (¡ bs₁≡)) (¡ xs≡)) sndₚ₁
  --                       in
  --                       uneraseDec
  --                         (≤-Reasoning.begin
  --                           length pre' ≤-Reasoning.≡⟨ cong length bs≡ ⟩
  --                           length (bs₁ ++ bs₂) ≤-Reasoning.≡⟨ length-++ bs₁ ⟩
  --                           length bs₁ + length bs₂ ≤-Reasoning.≤⟨ +-mono-≤ (¡ bs₁≤) (¡ bs₂≤) ⟩
  --                           r₁ + r₂ ≤-Reasoning.∎)
  --                         (_ ≤? _)
  --                     (inj₂ ¬b) → contradiction sndₚ₁ ¬b)
  --                   (_ ≤? _)

  -- parse&ᵈ : {@0 A : @0 List Σ → Set} {@0 B : (@0 bs : List Σ) → A bs → List Σ → Set}
  --           → @0 NoSubstrings A → @0 Unambiguous A
  --           → Parser (Logging ∘ Dec) A
  --           → (∀ {@0 bs} → Singleton (length bs) → (a : A bs) → MaximalParser (B bs a))
  --           → MaximalParser (&ₚᵈ A B)
  -- parse&ᵈ{A}{B} nn ua p₁ p₂ = mkMaximalParser help
  --   where
  --   module ≤ = ≤-Reasoning

  --   help : ∀ xs → Sigma _ _
  --   help xs =
  --     case runParser p₁ xs ret (const _) of λ where
  --       (mkLogged log (no ¬p)) →
  --         (mkLogged log (no (λ where
  --           (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} v₁ v₂ refl) suffix ps≡) →
  --             contradiction
  --               (success bs₁ _ refl v₁ (bs₂ ++ suffix)
  --                 (begin bs₁ ++ bs₂ ++ suffix ≡⟨ solve (++-monoid Σ) ⟩
  --                        (bs₁ ++ bs₂) ++ suffix ≡⟨⟩
  --                        prefix ++ suffix ≡⟨ ps≡ ⟩
  --                        xs ∎))
  --               ¬p)))
  --         , tt
  --       (mkLogged log₁ (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁))) →
  --         case runMaximalParser (p₂ (singleton r₁ r₁≡) v₁) suf₁ ret (const _) of λ where
  --           (mkLogged log₂ (no ¬p) , max) →
  --               mkLogged (log₁ ++ log₂) (no λ where
  --                 (success prefix read read≡ (mk&ₚ{bs₁'}{bs₂'} v₁' v₂' refl) suffix ps≡) →
  --                   let
  --                     xs≡ : Erased (pre₁ ++ suf₁ ≡ bs₁' ++ bs₂' ++ suffix)
  --                     xs≡ = ─ (begin
  --                       (pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩ 
  --                       xs ≡⟨ sym ps≡ ⟩
  --                       (bs₁' ++ bs₂') ++ suffix ≡⟨ solve (++-monoid Σ) ⟩
  --                       bs₁' ++ bs₂' ++ suffix ∎))

  --                     pre₁≡ : Erased (pre₁ ≡ bs₁')
  --                     pre₁≡ = ─ nn (¡ xs≡) v₁ v₁'

  --                     v₁≋ : _≋_{A = A} v₁ v₁'
  --                     v₁≋ = mk≋ (‼ (¡ pre₁≡)) (ua _ _)
  --                   in
  --                   case v₁≋ of λ where
  --                     ≋-refl →
  --                       contradiction (success bs₂' _ refl v₂' suffix (++-cancelˡ pre₁ (sym (¡ xs≡)))) ¬p)
  --             , tt
  --           (mkLogged log₂ (yes (success pre₂ r₂ r₂≡ v₂ suf₂ ps≡₂)) , max) →
  --               mkLogged (log₁ ++ log₂) (yes
  --                 (success (pre₁ ++ pre₂) (r₁ + r₂)
  --                   (begin (r₁ + r₂ ≡⟨ cong₂ _+_ r₁≡ r₂≡ ⟩
  --                          length pre₁ + length pre₂ ≡⟨ sym (length-++ pre₁) ⟩
  --                          length (pre₁ ++ pre₂) ∎))
  --                   (mk&ₚ v₁ v₂ refl) suf₂
  --                   (begin (pre₁ ++ pre₂) ++ suf₂ ≡⟨ solve (++-monoid Σ) ⟩
  --                        pre₁ ++ pre₂ ++ suf₂ ≡⟨ cong (pre₁ ++_) ps≡₂ ⟩
  --                        pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
  --                        xs ∎)))
  --             , λ where
  --               pre' suf' ps≡' (mk&ₚ{bs₁}{bs₂} fstₚ₁ sndₚ₁ bs≡) →
  --                 let
  --                   xs≡ : Erased (bs₁ ++ bs₂ ++ suf' ≡ pre₁ ++ suf₁)
  --                   xs≡ = ─ (begin (bs₁ ++ bs₂ ++ suf' ≡⟨ solve (++-monoid Σ) ⟩
  --                                  (bs₁ ++ bs₂) ++ suf' ≡⟨ cong (_++ suf') ∘ sym $ bs≡ ⟩
  --                                  pre' ++ suf' ≡⟨ ps≡' ⟩
  --                                  xs ≡⟨ sym ps≡₁ ⟩
  --                                  pre₁ ++ suf₁ ∎))

  --                   bs₁≡ : Erased (bs₁ ≡ pre₁)
  --                   bs₁≡ = ─ (nn (¡ xs≡) fstₚ₁ v₁)

  --                   v₁≡ : Erased ((bs₁ , fstₚ₁) ≡ (pre₁ , v₁))
  --                   v₁≡ = case bs₁≡ ret (const _) of λ where
  --                     (─ refl) →
  --                       case (‼ ua v₁ fstₚ₁) ret (const _) of λ where
  --                         refl → ─ refl
  --                 in
  --                 uneraseDec
  --                   (≤.begin
  --                     length pre' ≤.≡⟨ cong length bs≡ ⟩
  --                     length (bs₁ ++ bs₂) ≤.≡⟨ length-++ bs₁ ⟩
  --                     length bs₁ + length bs₂ ≤.≡⟨ cong (_+ length bs₂) (cong length (¡ bs₁≡)) ⟩
  --                     length pre₁ + length bs₂ ≤.≡⟨ cong (_+ length bs₂) (sym r₁≡) ⟩
  --                     r₁ + length bs₂
  --                       ≤.≤⟨ +-monoʳ-≤ r₁
  --                              (max bs₂ suf'
  --                                 (Lemmas.++-cancel≡ˡ bs₁ pre₁ (¡ bs₁≡) (¡ xs≡))
  --                                 (subst {A = Sigma (List Σ) A} (λ p → B (proj₁ p) (proj₂ p) bs₂ ) (¡ v₁≡) sndₚ₁))
  --                       ⟩
  --                     r₁ + r₂ ≤.∎)
  --                   (_ ≤? _)
        



  parseErased : ∀ {A : @0 List Σ → Set} → MaximalParser A → MaximalParser (λ x → Erased (A x))
  parseErased{A} p = mkMaximalParser help
    where
    help : ∀ xs → Sigma (Logging ∘ Dec $ Success (λ x → Erased (A x)) xs) (Lift _ GreatestSuccess)
    help xs =
      case
        _,e_{B = Lift (Success A xs) GreatestSuccess}
        (runParser (MaximalParser.parser p) xs)
        (MaximalParser.max p xs)
      ret (const _) of λ where
        (mkLogged log (no ¬p) , _) →
          (mkLogged log (no λ where
            (success prefix read read≡ (─ value) suffix ps≡) →
              contradiction (success prefix _ read≡ value suffix ps≡) ¬p))
          ,e tt
        (mkLogged log (yes p@(success prefix read read≡ value suffix ps≡)) , m) →
          mkLogged log (yes (success prefix _ read≡ (─ value) suffix ps≡))
          ,e λ where
               pre' suf' xs≡ (─ v) →
                 uneraseDec (m pre' suf' xs≡ v) (_ ≤? _)
