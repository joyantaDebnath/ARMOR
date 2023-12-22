open import Armor.Prelude
import      Data.Nat.Properties as Nat

module Armor.Grammar.Definitions.NoOverlap (Σ : Set) where

open ≡-Reasoning

NoOverlap : (A B : @0 List Σ → Set) → Set
NoOverlap A B =
  ∀ ws xs₁ ys₁ xs₂ ys₂ → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂
  → A (ws ++ xs₁) → A ws → (xs₁ ≡ []) ⊎ (¬ B xs₂)

noOverlapBoundary₁
  : ∀ {A B : @0 List Σ → Set} → NoOverlap A B
    → ∀ {ws xs₁ ys₁ xs₂ ys₂} → ws ++ xs₁ ++ ys₁ ≡ xs₂ ++ ys₂
    → A ws → B xs₁ → A xs₂
    → ws ≡ xs₂ ++ drop (length xs₂) ws
noOverlapBoundary₁{A} noo₁ {ws}{xs₁}{ys₁}{xs₂}{ys₂} ++≡ a₁ b₁ a₂ =
  ‼ Lemmas.drop-length-≤ xs₂ _ ws (xs₁ ++ ys₁) (sym ++≡) xs₂≤ws
  where
  @0 xs₂≤ws : length xs₂ ≤ length ws
  xs₂≤ws = Nat.≮⇒≥ noway
    where
    module _ (ws<xs₂ : length ws < length xs₂) where
      @0 xs₂≡ : xs₂ ≡ ws ++ drop (length ws) xs₂
      xs₂≡ = Lemmas.drop-length-≤ ws (xs₁ ++ ys₁) xs₂ ys₂ ++≡ (Nat.<⇒≤ ws<xs₂)

      noway : ⊥
      noway = ‼
        contradiction₂
          (noo₁ ws _ ys₂ xs₁ ys₁
            (++-cancelˡ ws
              (ws ++ drop (length ws) xs₂ ++ ys₂ ≡⟨ sym (++-assoc ws _ ys₂) ⟩
              (ws ++ drop (length ws) xs₂) ++ ys₂ ≡⟨ cong (_++ ys₂) (sym xs₂≡) ⟩
              xs₂ ++ ys₂ ≡⟨ sym ++≡ ⟩
              ws ++ xs₁ ++ ys₁ ∎))
            (subst₀! A xs₂≡ a₂) a₁)
          (λ ≡[] →
            contradiction
              (length ws ≡⟨ cong length (sym (++-identityʳ ws)) ⟩
              length (ws ++ []) ≡⟨ cong (λ x → length (ws ++ x)) (sym ≡[]) ⟩
              length (ws ++ drop (length ws) xs₂) ≡⟨ cong length (sym xs₂≡) ⟩
              length xs₂ ∎)
              (Nat.<⇒≢ ws<xs₂))
          (λ x → contradiction b₁ x)

noOverlapBoundary₂
  : ∀ {A B C : @0 List Σ → Set} → NoOverlap A B → NoOverlap A C
    → ∀ {xs₁ ys₁ zs₁ xs₂ ys₂ zs₂} → xs₁ ++ ys₁ ++ zs₁ ≡ xs₂ ++ ys₂ ++ zs₂
    → A xs₁ → B ys₁ → A xs₂ → C ys₂
    → xs₁ ≡ xs₂
noOverlapBoundary₂{A}{B}{C} noo₁ noo₂ {xs₁}{ys₁}{zs₁}{xs₂}{ys₂}{zs₂} ++≡ a₁ b₁ a₂ c₂ =
  case Nat.<-cmp (length xs₁) (length xs₂) ret (const _) of λ where
    (tri< xs₁<xs₂ _ _) →
      ‼ contradiction₂
        (noo₁ _ _ (ys₂ ++ zs₂) ys₁ zs₁ (Len<.++≡' xs₁<xs₂) (subst₀! A (Len<.xs₂≡ xs₁<xs₂) a₂) a₁)
        (λ ≡[] →
          contradiction
            (length xs₁ ≡⟨ cong length (sym (++-identityʳ xs₁)) ⟩
            length (xs₁ ++ []) ≡⟨ cong (λ x → length (xs₁ ++ x)) (sym ≡[]) ⟩
            length (xs₁ ++ drop (length xs₁) xs₂) ≡⟨ cong length (sym $ Len<.xs₂≡ xs₁<xs₂) ⟩
            length xs₂ ∎)
            (Nat.<⇒≢ xs₁<xs₂))
        (λ x → contradiction b₁ x)
    (tri≈ _ xs₁≡xs₂ _) → proj₁ (Lemmas.length-++-≡ _ _ _ _ ++≡ xs₁≡xs₂)
    (tri> _ _ xs₁>xs₂) →
      ‼ contradiction₂
        (noo₂ _ (drop (length xs₂) xs₁) (ys₁ ++ zs₁) _ zs₂
          (Len>.++≡' xs₁>xs₂)
          (subst₀! A (Len>.xs₁≡ xs₁>xs₂) a₁) a₂)
        (λ ≡[] →
          contradiction
            (length xs₂ ≡⟨ cong length (sym (++-identityʳ xs₂)) ⟩
            length (xs₂ ++ []) ≡⟨ cong (λ x → length (xs₂ ++ x)) (sym ≡[]) ⟩
            length (xs₂ ++ drop (length xs₂) xs₁) ≡⟨ cong length (sym $ Len>.xs₁≡ xs₁>xs₂) ⟩
            length xs₁ ∎)
            (Nat.<⇒≢ xs₁>xs₂))
        (λ x → contradiction c₂ x)
  where
  open ≡-Reasoning
  open import Tactic.MonoidSolver using (solve ; solve-macro)

  module Len< (xs₁<xs₂ : length xs₁ < length xs₂) where

    @0 xs₂≡ : xs₂ ≡ xs₁ ++ drop (length xs₁) xs₂
    xs₂≡ = Lemmas.drop-length-≤ xs₁ _ xs₂ _ ++≡ (Nat.<⇒≤ xs₁<xs₂)

    @0 ++≡' : drop (length xs₁) xs₂ ++ ys₂ ++ zs₂ ≡ ys₁ ++ zs₁
    ++≡' = ++-cancelˡ xs₁
      (xs₁ ++ drop (length xs₁) xs₂ ++ ys₂ ++ zs₂ ≡⟨ solve (++-monoid Σ) ⟩
      (xs₁ ++ drop (length xs₁) xs₂) ++ ys₂ ++ zs₂ ≡⟨ cong (_++ ys₂ ++ zs₂) (sym xs₂≡) ⟩
      xs₂ ++ ys₂ ++ zs₂ ≡⟨ sym ++≡ ⟩
      xs₁ ++ ys₁ ++ zs₁ ∎)
    
  module Len> (xs₁>xs₂ : length xs₁ > length xs₂) where

    @0 xs₁≡ : xs₁ ≡ xs₂ ++ drop (length xs₂) xs₁
    xs₁≡ = Lemmas.drop-length-≤ xs₂ _ xs₁ _ (sym ++≡) (Nat.<⇒≤ xs₁>xs₂)

    @0 ++≡' : drop (length xs₂) xs₁ ++ ys₁ ++ zs₁ ≡ ys₂ ++ zs₂
    ++≡' = ++-cancelˡ xs₂
      (xs₂ ++ drop (length xs₂) xs₁ ++ ys₁ ++ zs₁ ≡⟨ solve (++-monoid Σ) ⟩
      (xs₂ ++ drop (length xs₂) xs₁) ++ ys₁ ++ zs₁ ≡⟨ cong (_++ ys₁ ++ zs₁) (sym xs₁≡) ⟩
      xs₁ ++ ys₁ ++ zs₁ ≡⟨ ++≡ ⟩
      xs₂ ++ ys₂ ++ zs₂ ∎)
    
