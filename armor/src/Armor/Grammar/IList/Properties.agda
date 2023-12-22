import      Armor.Grammar.Definitions
import      Armor.Grammar.IList.TCB
import      Armor.Grammar.Option
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
import      Armor.Grammar.Sum
open import Armor.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Grammar.IList.Properties (Σ : Set) where

open Armor.Grammar.Definitions Σ
open Armor.Grammar.IList.TCB   Σ
open Armor.Grammar.Option      Σ
open Armor.Grammar.Properties  Σ
open Armor.Grammar.Seq         Σ
open Armor.Grammar.Sum         Σ

Rep : (@0 List Σ → Set) → @0 List Σ → Set
Rep A = Sum (λ x → Erased (x ≡ [])) (&ₚ A (IList A))

equiv : ∀ {A} → Equivalent (Rep A) (IList A)
proj₁ equiv (Sum.inj₁ (─ refl)) = nil
proj₁ equiv (Sum.inj₂ (mk&ₚ fstₚ₁ sndₚ₁ bs≡)) =
  consIList fstₚ₁ sndₚ₁ bs≡
proj₂ equiv nil = inj₁ (─ refl)
proj₂ equiv (consIList h t bs≡) =
  inj₂ (mk&ₚ h t bs≡)

iso : ∀ {A} → Iso (Rep A) (IList A)
proj₁ iso = equiv
proj₁ (proj₂ iso) (Sum.inj₁ (─ refl)) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (mk&ₚ fstₚ₁ sndₚ₁ bs≡)) = refl
proj₂ (proj₂ iso) nil = refl
proj₂ (proj₂ iso) (consIList h t bs≡) = refl

mapIListLength : ∀ {A B : @0 List Σ → Set} → (f : ∀ {@0 bs} → A bs → B bs) → ∀ {@0 bs} (xs : IList A bs)
                 → lengthIList (mapIList (λ {bs} → f{bs}) xs) ≡ lengthIList xs
mapIListLength f nil = refl
mapIListLength f (consIList _ t refl) = cong suc (mapIListLength f t)

@0 unambiguous : ∀ {@0 A} → Unambiguous A → NonEmpty A → NoSubstrings A → Unambiguous (IList A)
unambiguous ua ne nn nil nil = refl
unambiguous ua ne nn{xs} nil (cons (mkIListCons{bs₁}{bs₂} h t bs≡)) =
  contradiction (++-conicalˡ _ _ (sym bs≡)) (ne h)
unambiguous ua ne nn {xs} (cons (mkIListCons h t bs≡)) nil =
  contradiction (++-conicalˡ _ _ (sym bs≡)) (ne h)
unambiguous{A} ua ne nn (consIList{bs₁₁}{bs₁₂} h t bs≡) (consIList{bs₂₁}{bs₂₂} h₁ t₁ bs≡₁) =
  ≡-elim (λ {bs₂₁} bs₁≡ → ∀ h₁ bs≡₁ → _ ≡ cons (mkIListCons{bs₁ = bs₂₁} h₁ t₁ bs≡₁))
    (λ h₁ bs≡₁ →
      ≡-elim (λ {bs₂₂} bs₂≡ → ∀ t₁ bs≡₁ → _ ≡ cons (mkIListCons h₁ t₁ bs≡₁))
        (λ t₁ bs≡₁ →
          subst₂ (λ x y → _ ≡ cons (mkIListCons x y bs≡₁)) (ua h h₁) (unambiguous ua ne nn t t₁)
            (subst₀ (λ x → _ ≡ cons (mkIListCons _ _ x)) (≡-unique bs≡ bs≡₁) refl))
        bs₂≡ t₁ bs≡₁)
    bs₁≡ h₁ bs≡₁
  where
  @0 bs≡' : bs₁₁ ++ bs₁₂ ≡ bs₂₁ ++ bs₂₂
  bs≡' = trans₀ (sym bs≡) bs≡₁

  @0 bs₁≡ : bs₁₁ ≡ bs₂₁
  bs₁≡ = nn bs≡' h h₁

  bs₂≡ : bs₁₂ ≡ bs₂₂
  bs₂≡ = Lemmas.++-cancel≡ˡ _ _ bs₁≡ bs≡'

@0 unambiguousNOWF : ∀ {A} → Unambiguous A → NonEmpty A → NoOverlap A A → ∀ {xs} → (a₁ a₂ : IList A xs) → @0 Acc _<_ (lengthIList a₁) → a₁ ≡ a₂
  -- Unambiguous (IList A)
unambiguousNOWF ua ne noo nil nil _ = refl
unambiguousNOWF ua ne noo nil (consIList hd₂ tl₂ bs₂≡) _ =
    contradiction (++-conicalˡ _ _ (sym bs₂≡)) (ne hd₂)
unambiguousNOWF ua ne noo (consIList hd₁ tl₁ bs₁≡) nil _ =
  contradiction (++-conicalˡ _ _ (sym bs₁≡)) (ne hd₁)
unambiguousNOWF ua ne noo {bs} (consIList{bs₁₁} hd₁ nil bs₁≡) (consIList{bs₂₁} hd₂ nil bs₂≡) _ =
  caseErased bs≡ ret (const _) of λ where
    refl → ─ (caseErased ≡-unique bs₁≡ bs₂≡ ret (const _) of λ where
      refl → ─ (case ua hd₁ hd₂ ret (const _) of λ where
        refl → refl))
  where
  open ≡-Reasoning

  @0 bs≡ : bs₁₁ ≡ bs₂₁
  bs≡ = begin
    bs₁₁ ≡⟨ (sym $ ++-identityʳ bs₁₁) ⟩
    bs₁₁ ++ [] ≡⟨ sym bs₁≡ ⟩
    bs ≡⟨ bs₂≡ ⟩
    bs₂₁ ++ [] ≡⟨ ++-identityʳ bs₂₁ ⟩
    bs₂₁ ∎
unambiguousNOWF{A} ua ne noo {bs} (consIList{bs₁₁} hd₁ nil bs₁≡) (consIList{bs₂₁} hd₂ (consIList{bs₂₂}{bs₂₃} hd₂' tl₂ refl) bs₂≡) _ =
  contradiction bs₂₂≡[] (ne hd₂')
  where
  open ≡-Reasoning
  @0 bs≡ : bs₂₁ ++ bs₂₂ ++ bs₂₃ ≡ bs₁₁ ++ []
  bs≡ = begin
    bs₂₁ ++ (bs₂₂ ++ bs₂₃) ≡⟨ sym bs₂≡ ⟩
    bs ≡⟨ bs₁≡ ⟩
    bs₁₁ ++ [] ∎

  @0 bs₂₁≡ : bs₂₁ ≡ bs₁₁ ++ drop (length bs₁₁) bs₂₁
  bs₂₁≡ = noOverlapBoundary₁ noo bs≡ hd₂ hd₂' hd₁

  @0 bs≡' : bs₁₁ ++ drop (length bs₁₁) bs₂₁ ++ bs₂₂ ++ bs₂₃ ≡ bs₁₁ ++ []
  bs≡' = begin
    bs₁₁ ++ drop (length bs₁₁) bs₂₁ ++ bs₂₂ ++ bs₂₃ ≡⟨ (sym $ ++-assoc bs₁₁ (drop (length bs₁₁) bs₂₁) (bs₂₂ ++ bs₂₃)) ⟩
    (bs₁₁ ++ drop (length bs₁₁) bs₂₁) ++ bs₂₂ ++ bs₂₃ ≡⟨ cong (λ x → x ++ bs₂₂ ++ bs₂₃) (sym bs₂₁≡) ⟩
    bs₂₁ ++ bs₂₂ ++ bs₂₃ ≡⟨ bs≡ ⟩
    bs₁₁ ++ [] ∎

  @0 bs₂₂≡[] : bs₂₂ ≡ []
  bs₂₂≡[] = ++-conicalˡ bs₂₂ bs₂₃ (++-conicalʳ (drop (length bs₁₁) bs₂₁) (bs₂₂ ++ bs₂₃) (++-cancelˡ bs₁₁ bs≡'))

  -- lem₁ = noo bs₁₁ (drop (length bs₁₁) bs₂₁) (bs₂₂ ++ bs₂₃) {!!} {!!} {!!} (subst₀ A bs₂₁≡ hd₂) hd₁
unambiguousNOWF ua ne noo {bs} (consIList{bs₁₁} hd₁ (consIList{bs₁₂}{bs₁₃} hd₁' tl₁ refl) bs₁≡) (consIList{bs₂₁} hd₂ nil bs₂≡) _ =
  contradiction bs₁₂≡[] (ne hd₁')
  where
  open ≡-Reasoning
  @0 bs≡ : bs₁₁ ++ bs₁₂ ++ bs₁₃ ≡ bs₂₁ ++ []
  bs≡ = begin
    bs₁₁ ++ (bs₁₂ ++ bs₁₃) ≡⟨ sym bs₁≡ ⟩
    bs ≡⟨ bs₂≡ ⟩
    bs₂₁ ++ [] ∎

  @0 bs₁₁≡ : bs₁₁ ≡ bs₂₁ ++ drop (length bs₂₁) bs₁₁
  bs₁₁≡ = noOverlapBoundary₁ noo bs≡ hd₁ hd₁' hd₂

  @0 bs≡' : bs₂₁ ++ drop (length bs₂₁) bs₁₁ ++ bs₁₂ ++ bs₁₃ ≡ bs₂₁ ++ []
  bs≡' = begin
    bs₂₁ ++ drop (length bs₂₁) bs₁₁ ++ bs₁₂ ++ bs₁₃ ≡⟨ (sym $ ++-assoc bs₂₁ (drop (length bs₂₁) bs₁₁) (bs₁₂ ++ bs₁₃)) ⟩
    (bs₂₁ ++ drop (length bs₂₁) bs₁₁) ++ bs₁₂ ++ bs₁₃ ≡⟨ cong (λ x → x ++ bs₁₂ ++ bs₁₃) (sym bs₁₁≡) ⟩
    bs₁₁ ++ bs₁₂ ++ bs₁₃ ≡⟨ bs≡ ⟩
    bs₂₁ ++ [] ∎

  @0 bs₁₂≡[] : bs₁₂ ≡ []
  bs₁₂≡[] = ++-conicalˡ bs₁₂ bs₁₃ (++-conicalʳ (drop (length bs₂₁) bs₁₁) (bs₁₂ ++ bs₁₃) (++-cancelˡ bs₂₁ bs≡'))

unambiguousNOWF ua ne noo {bs}(consIList{bs₁₁}{bs₁₂'} hd₁ tl₁@(consIList{bs₁₂}{bs₁₃} hd₁' tl₁' bs₁≡') bs₁≡) (consIList{bs₂₁}{bs₂₂'} hd₂ tl₂@(consIList{bs₂₂}{bs₂₃} hd₂' tl₂' bs₂≡') bs₂≡) (WellFounded.acc rs) =
  caseErased bs₁₁≡bs₂₁ ret (const _) of λ where
    (refl , refl) → ─ (caseErased ua hd₁ hd₂ ret (const _) of λ where
      refl → ─ (caseErased ≡-unique bs₁≡ bs₂≡ ret (const _) of λ where
        refl → ─ (caseErased unambiguousNOWF ua ne noo tl₁ tl₂ (rs _ (s≤s ≤-refl)) ret (const _) of λ where
          refl → ─ refl)))
  where
  open ≡-Reasoning
  module ≤ = ≤-Reasoning

  @0 bs≡ : bs₂₁ ++ bs₂₂ ++ bs₂₃ ≡ bs₁₁ ++ bs₁₂ ++ bs₁₃
  bs≡ = begin
    bs₂₁ ++ (bs₂₂ ++ bs₂₃) ≡⟨ cong (bs₂₁ ++_) (sym bs₂≡') ⟩
    bs₂₁ ++ bs₂₂' ≡⟨ sym bs₂≡ ⟩
    bs ≡⟨ bs₁≡ ⟩
    bs₁₁ ++ bs₁₂' ≡⟨ cong (bs₁₁ ++_) bs₁≡' ⟩
    bs₁₁ ++ (bs₁₂ ++ bs₁₃) ∎

  @0 bs₂₁≡ : bs₂₁ ≡ bs₁₁ ++ drop (length bs₁₁) bs₂₁
  bs₂₁≡ = noOverlapBoundary₁ noo bs≡ hd₂ hd₂' hd₁

  @0 bs₁₁≡ : bs₁₁ ≡ bs₂₁ ++ drop (length bs₂₁) bs₁₁
  bs₁₁≡ = noOverlapBoundary₁ noo (sym bs≡) hd₁ hd₁' hd₂

  @0 bs₁₁≡' : bs₁₁ ≡ bs₁₁ ++ drop (length bs₁₁) bs₂₁ ++ drop (length bs₂₁) bs₁₁
  bs₁₁≡' = begin
    bs₁₁ ≡⟨ bs₁₁≡ ⟩
    bs₂₁ ++ drop (length bs₂₁) bs₁₁ ≡⟨ cong (_++ (drop (length bs₂₁) bs₁₁)) bs₂₁≡ ⟩
    (bs₁₁ ++ drop (length bs₁₁) bs₂₁) ++ drop (length bs₂₁) bs₁₁ ≡⟨ ++-assoc bs₁₁ (drop (length bs₁₁) bs₂₁) _ ⟩
    bs₁₁ ++ drop (length bs₁₁) bs₂₁ ++ drop (length bs₂₁) bs₁₁ ∎

  @0 lem : drop (length bs₁₁) bs₂₁ ++ drop (length bs₂₁) bs₁₁ ≡ []
  lem = ++-cancelˡ bs₁₁ (trans (sym bs₁₁≡') (sym (++-identityʳ bs₁₁)))

  @0 lem₁ : length bs₁₁ ≤ length bs₂₁
  lem₁ = ≤.begin
    (length bs₁₁ ≤.≤⟨ m≤m+n (length bs₁₁) (length (drop (length bs₁₁) bs₂₁)) ⟩
    length bs₁₁ + length (drop (length bs₁₁) bs₂₁) ≤.≡⟨ sym (length-++ bs₁₁) ⟩
    length (bs₁₁ ++ drop (length bs₁₁) bs₂₁) ≤.≡⟨ cong length (sym bs₂₁≡) ⟩
    length bs₂₁ ≤.∎)

  @0 lem₂ : length bs₂₁ ≤ length bs₁₁
  lem₂ = ≤.begin
    length bs₂₁ ≤.≤⟨ m≤m+n (length bs₂₁) (length (drop (length bs₂₁) bs₁₁)) ⟩
    length bs₂₁ + length (drop (length bs₂₁) bs₁₁) ≤.≡⟨ sym (length-++ bs₂₁) ⟩
    length (bs₂₁ ++ drop (length bs₂₁) bs₁₁) ≤.≡⟨ cong length (sym bs₁₁≡) ⟩
    length bs₁₁ ≤.∎

  @0 lem' : length bs₁₁ ≡ length bs₂₁
  lem' = ≤∧≮⇒≡ lem₁ (≤⇒≯ lem₂)

  @0 bs₁₁≡bs₂₁ : bs₁₁ ≡ bs₂₁ × bs₁₂' ≡ bs₂₂'
  bs₁₁≡bs₂₁ =
    let (pf₁ , pf₂) = Lemmas.length-++-≡ _ _ _ _ (sym bs≡) lem'
    in pf₁ , trans bs₁≡' (trans pf₂ (sym bs₂≡'))

@0 unambiguousNO : ∀ {A} → Unambiguous A → NonEmpty A → NoOverlap A A → Unambiguous (IList A)
unambiguousNO ua ne noo a₁ a₂ = unambiguousNOWF ua ne noo a₁ a₂ (<-wellFounded _)
  where open import Data.Nat.Induction

lengthIList≡
  : ∀ {@0 A} → NonEmpty A → NoSubstrings A
    → ∀ {@0 xs} → (il₁ il₂ : IList A xs)
    → lengthIList il₁ ≡ lengthIList il₂
lengthIList≡ ne nn nil nil = refl
lengthIList≡ ne nn nil (cons (mkIListCons head tail bs≡)) =
  contradiction
    (++-conicalˡ _ _ (sym bs≡))
    (ne head)
lengthIList≡ ne nn (cons (mkIListCons head tail bs≡)) nil =
  contradiction
    (++-conicalˡ _ _ (sym bs≡))
    (ne head)
lengthIList≡{A} ne nn (cons (mkIListCons{bs₂ = bs₂} head tail refl)) (cons (mkIListCons head₁ tail₁ bs≡₁)) =
  cong suc
    (trans (lengthIList≡ ne nn {bs₂} tail tail')
      (‼ ≡-elim (λ {bs₁'} eq → lengthIList (subst₀! (IList A) eq tail₁) ≡ lengthIList tail₁) refl bs₂≡))
  where
  @0 bs₁≡ : _ ≡ _
  bs₁≡ = nn (sym bs≡₁) head₁ head

  @0 bs₂≡ : _ ≡ _
  bs₂≡ = Lemmas.++-cancel≡ˡ _ _ bs₁≡ (sym bs≡₁)

  tail' : IList A bs₂
  tail' = subst₀! (IList A) bs₂≡ tail₁

lengthIList≤
  : ∀ {@0 A} → NonEmpty A → NoSubstrings A
    → (@0 xs₁ xs₂ : List Σ) {@0 ys₁ ys₂ : List Σ}
    → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂
    → @0 length xs₁ ≤ length xs₂
    → (v₁ : IList A xs₁) (v₂ : IList A xs₂)
    → lengthIList v₁ ≤ lengthIList v₂
lengthIList≤ ne nn .[] xs₂ ++≡ xs₁≤ nil v₂ = z≤n
lengthIList≤ ne nn .(bs₁ ++ bs₂) .[] ++≡ xs₁≤ (consIList{bs₁}{bs₂} head₁ tail₁ refl) nil =
  contradiction bs₁≡ (ne head₁)
  where
  @0 bs₁≡ : bs₁ ≡ []
  bs₁≡ = case (singleton bs₁ refl) of λ where
    (singleton [] refl) → refl
    (singleton (x ∷ x₁) refl) →
      contradiction xs₁≤ λ where ()
lengthIList≤ ne nn .(bs₁ ++ bs₂) xs₂{ys₁ = ys₁}{ys₂} ++≡ xs₁≤ (consIList{bs₁}{bs₂} head₁ tail₁ refl) (consIList{bs₁'}{bs₂'} head₂ tail₂ refl) =
  ≤.begin (1 + lengthIList tail₁
            ≤.≤⟨ +-monoʳ-≤ 1 (lengthIList≤ ne nn bs₂ bs₂'
                   (‼ Lemmas.++-cancel≡ˡ _ _ bs₁≡ ++≡')
                   bs₂≤ tail₁ tail₂) ⟩
          1 + lengthIList tail₂ ≤.∎)
  where
  open import Data.Nat.Properties
  open ≡-Reasoning
  module ≤ = ≤-Reasoning

  @0 ++≡' : bs₁ ++ bs₂ ++ ys₁ ≡ bs₁' ++ bs₂' ++ ys₂
  ++≡' =
    (begin bs₁ ++ bs₂ ++ ys₁ ≡⟨ solve (++-monoid Σ) ⟩
           (bs₁ ++ bs₂) ++ ys₁ ≡⟨ ++≡ ⟩
           (bs₁' ++ bs₂') ++ ys₂ ≡⟨ solve (++-monoid Σ) ⟩
           bs₁' ++ bs₂' ++ ys₂ ∎)

  @0 bs₁≡ : bs₁ ≡ bs₁'
  bs₁≡ = nn ++≡' head₁ head₂

  @0 bs₂≤ : length bs₂ ≤ length bs₂'
  bs₂≤ = +-cancelˡ-≤ (length bs₁)
           (≤.begin (length bs₁ + length bs₂ ≤.≡⟨ sym (length-++ bs₁) ⟩
                    length (bs₁ ++ bs₂) ≤.≤⟨ xs₁≤ ⟩
                    length (bs₁' ++ bs₂') ≤.≡⟨ length-++ bs₁' ⟩
                    length bs₁' + length bs₂' ≤.≡⟨ cong ((_+ _) ∘ length) (sym bs₁≡) ⟩
                    length bs₁ + length bs₂' ≤.∎))

private
  eqIListWF
    : ∀ {A : @0 List Σ → Set} ⦃ _ : Eq (Exists─ (List Σ) A) ⦄
      → {@0 xs ys : List Σ} (a₁ : IList A xs) (a₂ : IList A ys)
      → @0 Acc _<_ (lengthIList a₁)
      → Dec (_≡_{A = Exists─ (List Σ) (IList A)} (─ xs , a₁) (─ ys , a₂))
  eqIListWF nil nil (WellFounded.acc rs) = yes refl
  eqIListWF nil (consIList h t bs≡) (WellFounded.acc rs) = no λ ()
  eqIListWF (consIList h t bs≡) nil (WellFounded.acc rs) = no λ ()
  eqIListWF (consIList h t refl) (consIList h₁ t₁ refl) (WellFounded.acc rs)
    = case (─ _ ,e h) ≟ (─ _ ,e h₁) ret (const _) of λ where
        (no ¬p) → no λ where refl → contradiction refl ¬p
        (yes refl) →
          case eqIListWF t t₁ (rs _ ≤-refl) ret (const _) of λ where
            (no ¬p) → no λ where refl → contradiction refl ¬p
            (yes refl) → yes refl
    where
    open import Data.Nat.Properties hiding (_≟_)

IListEq : ∀ {A : @0 List Σ → Set} ⦃ _ : Eq (Exists─ (List Σ) A) ⦄
          → Eq (Exists─ (List Σ) (IList A))
Eq._≟_ IListEq (─ xs₁ , a₁) (─ xs₂ , a₂) = eqIListWF a₁ a₂ (<-wellFounded _)
  where open import Data.Nat.Induction

IListEq≋ : ∀ {A : @0 List Σ → Set} ⦃ _ : Eq≋ A ⦄ → Eq≋ (IList A)
IListEq≋ = Eq⇒Eq≋ (IListEq ⦃ Eq≋⇒Eq it ⦄)

@0 nonmalleable : ∀ {A : @0 List Σ → Set} {R : Raw A} → NonEmpty A → NoSubstrings A → NonMalleable R → NonMalleable (RawIList R)
nonmalleable {A} {R} ne nn N a₁ a₂ eq = noma a₁ a₂ eq (Nat.<-wellFounded _)
  where
  import Data.Nat.Induction as Nat

  noma : ∀ {@0 bs₁ bs₂} → (a₁ : IList A bs₁) (a₂ : IList A bs₂)
         → Raw.to (RawIList R) a₁ ≡ Raw.to (RawIList R) a₂
         → @0 Acc _<_ (lengthIList a₂)
         → _≡_{A = Exists─ (List Σ) (IList A)} (─ bs₁ , a₁) (─ bs₂ , a₂)
  noma nil nil eq (Nat.acc rs) = refl
  noma (consIList head₁ tail₁ refl) (consIList head₂ tail₂ refl) eq (Nat.acc rs) =
    case N head₁ head₂ (∷-injectiveˡ eq) ret (const _) of λ where
      refl → case ‼ noma tail₁ tail₂ (∷-injectiveʳ eq) (rs _ ≤-refl) ret (const _) of λ where
        refl → refl
