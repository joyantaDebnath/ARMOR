open import Armor.Binary
  renaming (module Base64 to B64)
open import Armor.Data.Base64
open import Armor.Data.PEM.CertText.Exclusions
open import Armor.Data.PEM.CertText.FinalLine
open import Armor.Data.PEM.CertText.FullLine
open import Armor.Data.PEM.CertText.TCB
open import Armor.Data.PEM.RFC5234
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Parallel
import      Armor.Grammar.Seq
open import Armor.Prelude
import      Data.List.Relation.Unary.Any.Properties as Any
import      Data.Nat.Properties as Nat
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.PEM.CertText.Properties where

open Armor.Grammar.Definitions          Char
open Armor.Grammar.IList                Char
open Armor.Grammar.Parallel             Char
open Armor.Grammar.Seq                  Char

open ≡-Reasoning

Rep : @0 List Char → Set
Rep = &ₚ (IList CertFullLine) CertFinalLine

equiv : Equivalent Rep CertText
proj₁ equiv (mk&ₚ body final bs≡) = mkCertText body final bs≡
proj₂ equiv (mkCertText body final bs≡) = mk&ₚ body final bs≡

iso : Iso Rep CertText
proj₁ iso = equiv
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkCertText body final bs≡) = refl

finalLineFromLines : ∀ {@0 bs} → IList CertFullLine bs → Erased (bs ≡ []) ⊎ &ₚ (IList CertFullLine) (CertFinalLine ×ₚ CertFullLine) bs
finalLineFromLines nil = inj₁ (─ refl)
finalLineFromLines (consIList{bs₁}{.[]} head₁ nil bs≡) =
  inj₂ (mk&ₚ nil (mk×ₚ (FinalLine.fromCertFullLine head₁) head₁)
          (begin (_ ≡⟨ bs≡ ⟩
                 bs₁ ++ [] ≡⟨ ++-identityʳ bs₁ ⟩
                 bs₁ ∎)))
finalLineFromLines{bs} (consIList{bs₁}{bs₂} head₁ tail₁@(consIList{bs₁ = bs₃} head₂ tail₂ bs≡₂) bs≡₁) =
  case finalLineFromLines tail₁ ret (const _) of λ where
    (inj₁ (─ refl)) →
      contradiction{P = bs₃ ≡ []} (++-conicalˡ bs₃ _ (sym bs≡₂)) (FullLine.nonempty head₂)
    (inj₂ (mk&ₚ{bs₅}{bs₆} fstₚ₁ sndₚ₁ refl)) →
      inj₂ (mk&ₚ (consIList head₁ fstₚ₁ refl) sndₚ₁
                    (begin _ ≡⟨ bs≡₁ ⟩
                           bs₁ ++ bs₅ ++ bs₆ ≡⟨ sym (++-assoc bs₁ bs₅ _) ⟩
                           (bs₁ ++ bs₅) ++ bs₆ ∎))

fullLineFromLine
  : ∀ {@0 xs₁ ys₁ xs₂ ys₂}
    → CertFinalLine xs₁ → CertFullLine xs₂
    → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂
    → CertFullLine xs₁
fullLineFromLine{xs₁}{ys₁}{xs₂}{ys₂} (mkCertFinalLine{l}{e} line lineLen eol bs≡) (mkCertFullLine{l₁}{e₁} line₁ eol₁ bs≡₁) ++≡ =
  mkCertFullLine (subst₀! (ExactLength (IList Base64Char) 64) (sym l≡) line₁) eol bs≡
  where
  @0 l≡ : l ≡ l₁
  l≡ = noOverlapBoundary₂ RFC5234.EOL.noOverlap RFC5234.EOL.noOverlap
         (l ++ e ++ ys₁ ≡⟨ sym (++-assoc l _ _) ⟩
         (l ++ e) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
         xs₁ ++ ys₁ ≡⟨ ++≡ ⟩
         xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
         (l₁ ++ e₁) ++ ys₂ ≡⟨ ++-assoc l₁ _ _ ⟩
         l₁ ++ e₁ ++ ys₂ ∎)
         line eol (Base64.Str.fromExactLength line₁) eol₁

@0 char∈ : ∀ {@0 b bs} → b ∈ bs → CertText bs → b ∈ B64.charset ++ String.toList "=\r\n"
char∈ b∈ (mkCertText{b₁}{f₁} body₁ final₁ refl) =
  caseErased Any.++⁻ b₁ b∈ ret (const _) of λ where
    (inj₁ x) → ─ FullLine.char∈List x body₁
    (inj₂ y) → ─ FinalLine.char∈ y final₁

@0 foldFinalIntoBodyWF
  : ∀ {@0 b₁ f₁ b₂ f₂ suf₁ suf₂}
    → IList CertFullLine b₁ → CertFinalLine f₁
    → (body₂ : IList CertFullLine b₂) → CertFinalLine f₂
    → Acc _<_ (lengthIList body₂)
    → b₁ ++ f₁ ++ suf₁ ≡ b₂ ++ f₂ ++ suf₂
    → length b₁ < length b₂
    → Σ[ n ∈ ℕ ] b₂ ≡ b₁ ++ f₁ ++ take n suf₁
foldFinalIntoBodyWF{f₁ = f₁}{f₂ = f₂}{suf₁}{suf₂} nil fin₁ (consIList{l₂}{b₂} fu₁ body₂ refl) fin₂ ac ++≡ b₁< =
    Lemmas.⊆⇒++take
      ++≡
      (caseErased singleton body₂ refl ret (const _) of λ where
        (singleton nil refl) → ─
          (≤.begin
            length f₁ ≤.≤⟨ Nat.m≤m+n (length f₁) _ ⟩
            length f₁ + length (drop (length f₁) l₂) ≤.≡⟨ sym (length-++ f₁) ⟩
            length (f₁ ++ drop (length f₁) l₂)
              ≤.≡⟨ cong length (f₁ ++ drop (length f₁) l₂ ≡ l₂ ∋ sym
                (noOverlapBoundary₁
                  FinalLine.noOverlap
                  (l₂ ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
                  (l₂ ++ []) ++ f₂ ++ suf₂ ≡⟨ sym ++≡ ⟩
                  f₁ ++ suf₁ ∎)
                  (FinalLine.fromCertFullLine fu₁) fin₂ fin₁))
              ⟩
            length l₂ ≤.≡⟨ cong length (sym (++-identityʳ l₂)) ⟩
            length (l₂ ++ []) ≤.∎)
        (singleton (consIList{l₂'}{b₂'} fu₂ body₂' refl) refl) → ─
          (≤.begin
            (length f₁ ≤.≤⟨ proj₂ (FinalLine.lengthRange fin₁) ⟩
            66 ≤.≤⟨ Nat.+-mono-≤ (proj₁ $ FullLine.fullLineLen fu₁) (Nat.≤-trans (s≤s z≤n) (proj₁ $ FullLine.fullLineLen fu₂)) ⟩
            length l₂ + length l₂' ≤.≡⟨ sym (length-++ l₂) ⟩
            length (l₂ ++ l₂') ≤.≤⟨ Nat.m≤m+n _ _ ⟩
            length (l₂ ++ l₂') + length b₂' ≤.≡⟨ sym (length-++ (l₂ ++ l₂')) ⟩
            length ((l₂ ++ l₂') ++ b₂') ≤.≡⟨ cong length (++-assoc l₂ l₂' _) ⟩
            length (l₂ ++ l₂' ++ b₂') ≤.∎)))
  where
  module ≤ = Nat.≤-Reasoning
  
foldFinalIntoBodyWF{f₁ = f₁}{f₂ = f₂}{suf₁}{suf₂} (consIList{u₁}{b₁} fu₁ nil refl) fin₁ (consIList{u₂}{b₂} fu₂ nil refl) fin₂ ac ++≡ b₁< =
  contradiction
    (cong length (u₁ ≡ u₂ ∋
      noOverlapBoundary₂ noOverlapLines noOverlapLines ++≡' fu₁ fin₁ fu₂ fin₂))
    (Nat.<⇒≢
      (≤.begin
        suc (length u₁) ≤.≡⟨ cong (suc ∘ length) (sym (++-identityʳ u₁)) ⟩
        suc (length (u₁ ++ [])) ≤.≤⟨ b₁< ⟩
        length (u₂ ++ []) ≤.≡⟨ cong length (++-identityʳ u₂) ⟩
        length u₂ ≤.∎))
  where
  module ≤ = Nat.≤-Reasoning

  @0 ++≡' : u₁ ++ f₁ ++ suf₁ ≡ u₂ ++ f₂ ++ suf₂
  ++≡' =
    u₁ ++ f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
    (u₁ ++ []) ++ f₁ ++ suf₁ ≡⟨ ++≡ ⟩
    (u₂ ++ []) ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
    u₂ ++ f₂ ++ suf₂ ∎
foldFinalIntoBodyWF{f₁ = f₁}{f₂ = f₂}{suf₁}{suf₂} (consIList{u₁}{b₁} fu₁ nil refl) fin₁ (consIList{u₂}{b₂} fu₂ (consIList{u₂'}{b₂'} fu₂' body₂ refl) refl) fin₂ (WellFounded.acc rs) ++≡ b₁< =
  (proj₁ ih) ,
    (u₂ ++ u₂' ++ b₂' ≡⟨ cong (u₂ ++_) (proj₂ ih) ⟩
    u₂ ++ f₁ ++ take (proj₁ ih) suf₁ ≡⟨ cong (_++ f₁ ++ take (proj₁ ih) suf₁) (sym u₁≡) ⟩
    u₁ ++ f₁ ++ take (proj₁ ih) suf₁ ≡⟨ solve (++-monoid Char) ⟩
    (u₁ ++ []) ++ f₁ ++ take (proj₁ ih) suf₁ ∎)
  where
  module ≤ = Nat.≤-Reasoning

  @0 ++≡' : u₁ ++ b₁ ++ f₁ ++ suf₁ ≡ u₂ ++ u₂' ++ b₂' ++ f₂ ++ suf₂
  ++≡' = u₁ ++ b₁ ++ f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
         (u₁ ++ []) ++ f₁ ++ suf₁ ≡⟨ ++≡ ⟩
         (u₂ ++ u₂' ++ b₂') ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
         u₂ ++ u₂' ++ b₂' ++ f₂ ++ suf₂ ∎

  @0 u₁≡ : u₁ ≡ u₂
  u₁≡ = noOverlapBoundary₂ noOverlapLines FullLine.nooverlap ++≡' fu₁ fin₁ fu₂ fu₂'

  @0 ++≡ᵤ : f₁ ++ suf₁ ≡ u₂' ++ b₂' ++ f₂ ++ suf₂
  ++≡ᵤ = Lemmas.++-cancel≡ˡ _ _ u₁≡ ++≡'

  b₁<' : length u₁ + 0 < length u₁ + length (u₂' ++ b₂')
  b₁<' = ≤.begin
    (suc (length u₁ + 0) ≤.≡⟨ cong suc (sym (length-++ u₁)) ⟩
    suc (length (u₁ ++ [])) ≤.≤⟨ b₁< ⟩
    length (u₂ ++ u₂' ++ b₂') ≤.≡⟨ length-++ u₂ ⟩
    length u₂ + length (u₂' ++ b₂') ≤.≡⟨ cong (_+ length (u₂' ++ b₂')) (cong length (sym u₁≡)) ⟩
    length u₁ + length (u₂' ++ b₂') ≤.∎)

  ih = foldFinalIntoBodyWF nil fin₁ (consIList fu₂' body₂ refl) fin₂ (rs _ Nat.≤-refl)
         (f₁ ++ suf₁ ≡⟨ ++≡ᵤ ⟩
         u₂' ++ b₂' ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
         (u₂' ++ b₂') ++ f₂ ++ suf₂ ∎)
         (Nat.+-cancelˡ-< (length u₁) b₁<')

foldFinalIntoBodyWF{f₁ = f₁}{f₂ = f₂}{suf₁}{suf₂} (consIList{u₁}{b₁} fu₁ (consIList{u₁'}{b₁'} fu₁' body₁ refl) refl) fin₁ (consIList{u₂}{b₂} fu₂ nil refl) fin₂ ac ++≡ b₁< =
  contradiction{P = length (u₁' ++ b₁') < 0}
    (Nat.+-cancelˡ-< (length u₁) (≤.begin
      (1 + length u₁ + length (u₁' ++ b₁') ≤.≡⟨ cong suc (sym (length-++ u₁)) ⟩
      1 + length (u₁ ++ u₁' ++ b₁') ≤.≤⟨ b₁< ⟩
      length (u₂ ++ []) ≤.≡⟨ length-++ u₂ ⟩
      length u₂ + 0 ≤.≡⟨ cong (λ x → length x + 0) (sym u₁≡) ⟩
      length u₁ + 0 ≤.∎)))
    λ ()
  where
  module ≤ = Nat.≤-Reasoning

  b₁<' : length u₁ + length (u₁' ++ b₁') < length u₂ + 0
  b₁<' = ≤.begin
    (1 + length u₁ + length (u₁' ++ b₁') ≤.≡⟨ cong suc (sym (length-++ u₁)) ⟩
    1 + length (u₁ ++ u₁' ++ b₁') ≤.≤⟨ b₁< ⟩
    length (u₂ ++ []) ≤.≡⟨ length-++ u₂ ⟩
    length u₂ + 0 ≤.∎)

  ++≡' : u₁ ++ u₁' ++ b₁' ++ f₁ ++ suf₁ ≡ u₂ ++ f₂ ++ suf₂
  ++≡' = u₁ ++ u₁' ++ b₁' ++ f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
         (u₁ ++ u₁' ++ b₁') ++ f₁ ++ suf₁ ≡⟨ ++≡ ⟩
         (u₂ ++ []) ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
         u₂ ++ f₂ ++ suf₂ ∎

  u₁≡ : u₁ ≡ u₂
  u₁≡ = noOverlapBoundary₂ FullLine.nooverlap noOverlapLines ++≡' fu₁ fu₁' fu₂ fin₂

  ++≡ᵤ : u₁' ++ b₁' ++ f₁ ++ suf₁ ≡ f₂ ++ suf₂
  ++≡ᵤ = Lemmas.++-cancel≡ˡ _ _ u₁≡ ++≡'

foldFinalIntoBodyWF{f₁ = f₁}{f₂ = f₂}{suf₁}{suf₂} (consIList{u₁}{b₁} fu₁ (consIList{u₁'}{b₁'} fu₁' body₁ refl) refl) fin₁ (consIList{u₂}{b₂} fu₂ (consIList{u₂'}{b₂'} fu₂' body₂ refl) refl) fin₂ (WellFounded.acc rs) ++≡ b₁< =
  proj₁ ih ,
    (u₂ ++ u₂' ++ b₂' ≡⟨ cong (u₂ ++_) (proj₂ ih) ⟩
    u₂ ++ (u₁' ++ b₁') ++ f₁ ++ take (proj₁ ih) suf₁ ≡⟨ cong (_++ ((u₁' ++ b₁') ++ f₁ ++ take (proj₁ ih) suf₁)) (sym u₁≡) ⟩
    u₁ ++ (u₁' ++ b₁') ++ f₁ ++ take (proj₁ ih) suf₁ ≡⟨ cong (u₁ ++_) (++-assoc u₁' _ _) ⟩
    u₁ ++ u₁' ++ b₁' ++ f₁ ++ take (proj₁ ih) suf₁ ≡⟨ sym (++-assoc u₁ u₁' _) ⟩
    (u₁ ++ u₁') ++ b₁' ++ f₁ ++ take (proj₁ ih) suf₁ ≡⟨ sym (++-assoc (u₁ ++ u₁') _ _) ⟩
    ((u₁ ++ u₁') ++ b₁') ++ f₁ ++ take (proj₁ ih) suf₁ ≡⟨ cong (_++ f₁ ++ take (proj₁ ih) suf₁) (++-assoc u₁ u₁' _) ⟩
    (u₁ ++ u₁' ++ b₁') ++ f₁ ++ take (proj₁ ih) suf₁ ∎)
  where
  module ≤ = Nat.≤-Reasoning

  ++≡' : u₁ ++ u₁' ++ b₁' ++ f₁ ++ suf₁ ≡ u₂ ++ u₂' ++ b₂' ++ f₂ ++ suf₂
  ++≡' = u₁ ++ u₁' ++ b₁' ++ f₁ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
         (u₁ ++ u₁' ++ b₁') ++ f₁ ++ suf₁ ≡⟨ ++≡ ⟩
         (u₂ ++ u₂' ++ b₂') ++ f₂ ++ suf₂ ≡⟨ solve (++-monoid Char) ⟩
         u₂ ++ u₂' ++ b₂' ++ f₂ ++ suf₂ ∎

  u₁≡ : u₁ ≡ u₂
  u₁≡ = noOverlapBoundary₂ FullLine.nooverlap FullLine.nooverlap ++≡' fu₁ fu₁' fu₂ fu₂'

  ++≡ᵤ : (u₁' ++ b₁') ++ f₁ ++ suf₁ ≡ (u₂' ++ b₂') ++ f₂ ++ suf₂
  ++≡ᵤ = trans (++-assoc u₁' b₁' _) (trans (Lemmas.++-cancel≡ˡ _ _ u₁≡ ++≡') (sym (++-assoc u₂' b₂' _)))

  b₁<' : length (u₁' ++ b₁') < length (u₂' ++ b₂')
  b₁<' = Nat.+-cancelˡ-< (length u₁) (≤.begin
    (1 + length u₁ + length (u₁' ++ b₁') ≤.≡⟨ sym (cong suc (length-++ u₁)) ⟩
    1 + length (u₁ ++ u₁' ++ b₁') ≤.≤⟨ b₁< ⟩
    length (u₂ ++ u₂' ++ b₂') ≤.≡⟨ length-++ u₂ ⟩
    length u₂ + length (u₂' ++ b₂') ≤.≡⟨ cong (λ x → length x + length (u₂' ++ b₂')) (sym u₁≡) ⟩
    length u₁ + length (u₂' ++ b₂') ≤.∎))

  ih = foldFinalIntoBodyWF (consIList fu₁' body₁ refl) fin₁ (consIList fu₂' body₂ refl) fin₂ (rs _ Nat.≤-refl) ++≡ᵤ b₁<'

@0 foldFinalIntoBody
  : ∀ {@0 b₁ f₁ b₂ f₂ suf₁ suf₂}
    → IList CertFullLine b₁ → CertFinalLine f₁
    → IList CertFullLine b₂ → CertFinalLine f₂
    → b₁ ++ f₁ ++ suf₁ ≡ b₂ ++ f₂ ++ suf₂
    → length b₁ < length b₂
    → Σ[ n ∈ ℕ ] b₂ ≡ b₁ ++ f₁ ++ take n suf₁
foldFinalIntoBody fu₁ fi₁ fu₂ fi₂ ++≡ b₁< = foldFinalIntoBodyWF fu₁ fi₁ fu₂ fi₂ (<-wellFounded (lengthIList fu₂)) ++≡ b₁<
  where open import Data.Nat.Induction

@0 body< : ∀ {@0 b₁ f₁ b₂ f₂ suf₁ suf₂}
        → IList CertFullLine b₁ → CertFinalLine f₁
        → IList CertFullLine b₂ → CertFinalLine f₂
        → b₁ ++ f₁ ++ suf₁ ≡ b₂ ++ f₂ ++ suf₂
        → length b₁ < length b₂
        → length b₁ + length f₁ ≤ length b₂ + length f₂
body<{b₁}{f₁}{b₂}{f₂}{suf₁}{suf₂} body₁ fin₁ body₂ fin₂ ++≡ b₁< =
  ≤.begin
    length b₁ + length f₁ ≤.≤⟨ Nat.m≤m+n (length b₁ + length f₁) _ ⟩
    (length b₁ + length f₁) + length (take (proj₁ lem) suf₁) ≤.≡⟨ cong (_+ (length (take (proj₁ lem) suf₁))) (sym (length-++ b₁)) ⟩
    length (b₁ ++ f₁) + length (take (proj₁ lem) suf₁) ≤.≡⟨ sym (length-++ (b₁ ++ f₁)) ⟩
    length ((b₁ ++ f₁) ++ take (proj₁ lem) suf₁) ≤.≡⟨ cong length (++-assoc b₁ f₁ _) ⟩
    length (b₁ ++ f₁ ++ take (proj₁ lem) suf₁) ≤.≡⟨ cong length (sym (proj₂ lem)) ⟩
    length b₂ ≤.≤⟨ Nat.m≤m+n (length b₂) (length f₂) ⟩
    length b₂ + length f₂ ≤.∎
  where
  module ≤ = Nat.≤-Reasoning

  lem = foldFinalIntoBody body₁ fin₁ body₂ fin₂ ++≡ b₁<

@0 unambiguous : Unambiguous CertText
unambiguous =
  Iso.unambiguous iso (λ c₁ c₂ → uaWF c₁ c₂ (<-wellFounded _))
  where
  open import Data.Nat.Induction using (<-wellFounded)
  open ≡-Reasoning

  @0 uaWF : ∀ {xs} → (c₁ c₂ : Rep xs) → @0 Acc _<_ (lengthIList (fstₚ c₁)) → c₁ ≡ c₂
  uaWF (mk&ₚ nil final₁ refl) (mk&ₚ nil final₂ refl) ac =
    case FinalLine.unambiguous final₁ final₂ of λ where
      refl → refl
  uaWF {xs} (mk&ₚ nil final₁ refl) (mk&ₚ{bs₂ = bs₂₃} (consIList{bs₂₁}{bs₂₂} line₂ lines₂ refl) final₂ bs≡₂) ac =
    case (singleton lines₂ refl) of λ where
      (singleton nil refl) →
        ‼ contradiction₂
          (noOverlapLines bs₂₁ _ [] _ [] refl (subst₀! CertFullLine xs≡ line₁) line₂)
          (FinalLine.nonempty final₂)
          (λ ¬final₂ → ¬final₂ final₂)
      (singleton (consIList{bs₂₂₁}{bs₂₂₂} line₂' lines₂' refl) refl) →
        let @0 xs≡' : ((bs₂₂₁ ++ bs₂₂₂) ++ bs₂₃) ++ [] ≡ bs₂₂₁ ++ bs₂₂₂ ++ bs₂₃
            xs≡' = begin
              ((bs₂₂₁ ++ bs₂₂₂) ++ bs₂₃) ++ [] ≡⟨ ++-identityʳ _ ⟩
              (bs₂₂₁ ++ bs₂₂₂) ++ bs₂₃ ≡⟨ ++-assoc bs₂₂₁ _ _ ⟩
              bs₂₂₁ ++ bs₂₂₂ ++ bs₂₃ ∎
        in
        ‼ contradiction₂
          (FullLine.nooverlap _ _ [] _ (bs₂₂₂ ++ bs₂₃) xs≡' (subst₀! CertFullLine xs≡ line₁) line₂)
          (λ ≡[] → contradiction (++-conicalʳ _ _ ≡[]) (FinalLine.nonempty final₂))
          λ ¬line₂' → ¬line₂' line₂'
    where
    @0 xs≡ : xs ≡ bs₂₁ ++ bs₂₂ ++ bs₂₃
    xs≡ = trans bs≡₂ (++-assoc bs₂₁ bs₂₂ bs₂₃)

    line₁ : CertFullLine xs
    line₁ = fullLineFromLine final₁ line₂ (trans (++-identityʳ xs) xs≡)
  uaWF {xs} (mk&ₚ{bs₂ = bs₁₃} (consIList{bs₁₁}{bs₁₂} line₁ lines₁ refl) final₁ bs≡₁) (mk&ₚ nil final₂ refl) ac =
    case (singleton lines₁ refl) of λ where
      (singleton nil refl) →
        ‼ contradiction₂
          (noOverlapLines bs₁₁ _ [] _ [] refl (subst₀! CertFullLine xs≡ line₂) line₁)
          (FinalLine.nonempty final₁)
          λ ¬final₁ → ¬final₁ final₁
      (singleton (consIList{bs₁₂₁}{bs₁₂₂} line₁' lines₁' refl) refl) →
        let @0 xs≡' : ((bs₁₂₁ ++ bs₁₂₂) ++ bs₁₃) ++ [] ≡ bs₁₂₁ ++ bs₁₂₂ ++ bs₁₃
            xs≡' = begin
              (((bs₁₂₁ ++ bs₁₂₂) ++ bs₁₃) ++ [] ≡⟨ ++-identityʳ _ ⟩
              (bs₁₂₁ ++ bs₁₂₂) ++ bs₁₃ ≡⟨ ++-assoc bs₁₂₁ _ _ ⟩
              bs₁₂₁ ++ bs₁₂₂ ++ bs₁₃ ∎)
        in
        ‼ contradiction₂
          (FullLine.nooverlap _ _ [] _ (bs₁₂₂ ++ bs₁₃) xs≡' (subst₀! CertFullLine xs≡ line₂) line₁)
          (λ ≡[] → contradiction (++-conicalʳ _ _ ≡[]) (FinalLine.nonempty final₁))
          λ ¬line₁' → ¬line₁' line₁'
    where
    @0 xs≡ : xs ≡ bs₁₁ ++ bs₁₂ ++ bs₁₃
    xs≡ = trans bs≡₁ (++-assoc bs₁₁ _ _)

    line₂ : CertFullLine xs
    line₂ = fullLineFromLine final₂ line₁ (trans (++-identityʳ xs) xs≡)
  uaWF (mk&ₚ{bs₂ = bs₁₃} (consIList{bs₁₁} line₁ nil refl) final₁ bs≡₁) (mk&ₚ{bs₂ = bs₂₃} (consIList{bs₂₁} line₂ nil refl) final₂ bs≡₂) ac =
    case (((trans bs≡₁ (cong (_++ bs₁₃) (++-identityʳ bs₁₁)))) ,′ ((trans bs≡₂ (cong (_++ bs₂₃) (++-identityʳ bs₂₁))))) of λ where
      (bs≡₁' , bs≡₂') → case ‼ Seq.unambiguousNO FullLine.unambiguous FinalLine.unambiguous noOverlapLines (mk&ₚ line₁ final₁ bs≡₁') (mk&ₚ line₂ final₂ bs≡₂') of λ where
        refl → case ‼ ≡-unique bs≡₁ bs≡₂ ret (const _) of λ where
          refl → refl
  uaWF {xs} (mk&ₚ{bs₂ = bs₁₃} (consIList{bs₁₁} line₁ nil refl) final₁ bs≡₁) (mk&ₚ{bs₂ = bs₂₃} (consIList{bs₂₁} line₂ (consIList{bs₂₂₁}{bs₂₂₂} line₂' lines₂ refl) refl) final₂ bs≡₂) ac =
    case (singleton lines₂ refl) of λ where
      (singleton nil refl) →
        ‼ contradiction₂
          (noOverlapLines _ _ [] _ [] refl (subst₀! CertFullLine (proj₂ xs≡×) line₁') line₂')
          (FinalLine.nonempty final₂)
          λ ¬final₂ → ¬final₂ final₂
      (singleton (consIList{bs₂₂₂₁}{bs₂₂₂₂} line₂“ lines refl) refl) →
        let @0 xs≡' : ((bs₂₂₂₁ ++ bs₂₂₂₂) ++ bs₂₃) ++ [] ≡ bs₂₂₂₁ ++ bs₂₂₂₂ ++ bs₂₃
            xs≡' = begin
              ((bs₂₂₂₁ ++ bs₂₂₂₂) ++ bs₂₃) ++ [] ≡⟨ ++-identityʳ _ ⟩
              (bs₂₂₂₁ ++ bs₂₂₂₂) ++ bs₂₃ ≡⟨ ++-assoc bs₂₂₂₁ _ _ ⟩
              bs₂₂₂₁ ++ bs₂₂₂₂ ++ bs₂₃ ∎
        in
        ‼ contradiction₂
          (FullLine.nooverlap _ _ [] _ (bs₂₂₂₂ ++ bs₂₃) xs≡' (subst₀! CertFullLine (proj₂ xs≡×) line₁') line₂')
          (λ ≡[] → contradiction (++-conicalʳ _ _ ≡[]) (FinalLine.nonempty final₂))
          (λ ¬line₂“ → ¬line₂“ line₂“)
    where
    import Data.Nat.Properties as Nat
    module ≤ = Nat.≤-Reasoning
    @0 xs≡ : bs₁₁ ++ bs₁₃ ≡ bs₂₁ ++ bs₂₂₁ ++ bs₂₂₂ ++ bs₂₃
    xs≡ = begin
      bs₁₁ ++ bs₁₃ ≡⟨ cong (_++ bs₁₃) (sym (++-identityʳ bs₁₁)) ⟩
      (bs₁₁ ++ []) ++ bs₁₃ ≡⟨ sym bs≡₁ ⟩
      xs ≡⟨ bs≡₂ ⟩
      (bs₂₁ ++ bs₂₂₁ ++ bs₂₂₂) ++ bs₂₃ ≡⟨ sym (Lemmas.++-assoc₄ bs₂₁ bs₂₂₁ _ _) ⟩
      _ ∎

    @0 xs≡× : bs₁₁ ≡ bs₂₁ × bs₁₃ ≡ bs₂₂₁ ++ bs₂₂₂ ++ bs₂₃
    xs≡× =
      Lemmas.length-++-≡ _ _ _ _ xs≡
        (Nat.≤-antisym
          (≤.begin
            length bs₁₁ ≤.≤⟨ Nat.m≤m+n _ _ ⟩
            length bs₁₁ + length (drop (length bs₁₁) bs₂₁) ≤.≡⟨ sym (length-++ bs₁₁) ⟩
            length (bs₁₁ ++ drop (length bs₁₁) bs₂₁) ≤.≡⟨ cong length (sym (noOverlapBoundary₁ FullLine.nooverlap {ws = bs₂₁} (sym xs≡) line₂ line₂' line₁)) ⟩
            length bs₂₁ ≤.∎)
          (≤.begin
            (length bs₂₁ ≤.≤⟨ Nat.m≤m+n _ _ ⟩
            length bs₂₁ + length (drop (length bs₂₁) bs₁₁) ≤.≡⟨ sym (length-++ bs₂₁) ⟩
            length (bs₂₁ ++ drop (length bs₂₁) bs₁₁) ≤.≡⟨ cong length (sym (noOverlapBoundary₁ noOverlapLines (trans (cong (bs₁₁ ++_) (++-identityʳ bs₁₃)) xs≡) line₁ final₁ line₂)) ⟩
            length bs₁₁ ≤.∎)))

    line₁' : CertFullLine bs₁₃
    line₁' = fullLineFromLine final₁ line₂' (trans (++-identityʳ bs₁₃) (proj₂ xs≡×))
  uaWF {xs} (mk&ₚ{bs₂ = bs₁₃} (consIList{bs₁₁} line₁ (consIList{bs₁₂₁}{bs₁₂₂} line₁' lines₁ refl) refl) final₁ bs≡₁) (mk&ₚ{bs₂ = bs₂₃} (consIList{bs₂₁} line₂ nil refl) final₂ bs≡₂) ac =
    case (singleton lines₁ refl) of λ where
      (singleton nil refl) → 
        ‼ contradiction₂
          (noOverlapLines _ _ [] _ [] refl (subst₀! CertFullLine (proj₂ xs≡×) line₂') line₁')
          (FinalLine.nonempty final₁)
          λ ¬final₁ → ¬final₁ final₁
      (singleton (consIList{bs₁₂₂₁}{bs₁₂₂₂} line₁“ lines₁ refl) refl) →
        let @0 xs≡' : ((bs₁₂₂₁ ++ bs₁₂₂₂) ++ bs₁₃) ++ [] ≡ bs₁₂₂₁ ++ bs₁₂₂₂ ++ bs₁₃
            xs≡' = begin
              ((bs₁₂₂₁ ++ bs₁₂₂₂) ++ bs₁₃) ++ [] ≡⟨ ++-identityʳ _ ⟩
              (bs₁₂₂₁ ++ bs₁₂₂₂) ++ bs₁₃ ≡⟨ ++-assoc bs₁₂₂₁ _ _ ⟩
              _ ∎
        in
        ‼ contradiction₂
          (FullLine.nooverlap _ _ [] _ (bs₁₂₂₂ ++ bs₁₃) xs≡' (subst₀! CertFullLine (proj₂ xs≡×) line₂') line₁')
          (λ ≡[] → contradiction (++-conicalʳ _ _ ≡[]) (FinalLine.nonempty final₁))
          (λ ¬line₁“ → ¬line₁“ line₁“) 
    where
    import Data.Nat.Properties as Nat
    module ≤ = Nat.≤-Reasoning
    @0 xs≡ : bs₂₁ ++ bs₂₃ ≡ bs₁₁ ++ bs₁₂₁ ++ bs₁₂₂ ++ bs₁₃
    xs≡ = begin
      bs₂₁ ++ bs₂₃ ≡⟨ cong (_++ bs₂₃) (sym (++-identityʳ bs₂₁)) ⟩
      (bs₂₁ ++ []) ++ bs₂₃ ≡⟨ sym bs≡₂ ⟩
      xs ≡⟨ bs≡₁ ⟩
      (bs₁₁ ++ bs₁₂₁ ++ bs₁₂₂) ++ bs₁₃ ≡⟨ sym (Lemmas.++-assoc₄ bs₁₁ bs₁₂₁ _ _) ⟩
      _ ∎

    @0 xs≡× : bs₂₁ ≡ bs₁₁ × bs₂₃ ≡ bs₁₂₁ ++ bs₁₂₂ ++ bs₁₃
    xs≡× =
      Lemmas.length-++-≡ _ _ _ _ xs≡
        (Nat.≤-antisym
          (≤.begin
            length bs₂₁ ≤.≤⟨ Nat.m≤m+n _ _ ⟩
            length bs₂₁ + length (drop (length bs₂₁) bs₁₁) ≤.≡⟨ sym (length-++ bs₂₁) ⟩
            length (bs₂₁ ++ drop (length bs₂₁) bs₁₁) ≤.≡⟨ cong length (sym (noOverlapBoundary₁ FullLine.nooverlap {ws = bs₁₁} (sym xs≡) line₁ line₁' line₂)) ⟩
            length bs₁₁ ≤.∎)
          (≤.begin
            (length bs₁₁ ≤.≤⟨ Nat.m≤m+n _ _ ⟩
            length bs₁₁ + length (drop (length bs₁₁) bs₂₁) ≤.≡⟨ sym (length-++ bs₁₁) ⟩
            length (bs₁₁ ++ drop (length bs₁₁) bs₂₁) ≤.≡⟨ cong length (sym (noOverlapBoundary₁ noOverlapLines (trans (cong (bs₂₁ ++_) (++-identityʳ bs₂₃)) xs≡) line₂ final₂ line₁)) ⟩
            length bs₂₁ ≤.∎)))

    line₂' : CertFullLine bs₂₃
    line₂' = fullLineFromLine final₂ line₁' (trans (++-identityʳ bs₂₃) (proj₂ xs≡×))
  uaWF {xs} (mk&ₚ{bs₂ = bs₁₃} (consIList{bs₁₁} line₁ (consIList{bs₁₂₁}{bs₁₂₂} line₁' lines₁ refl) refl) final₁ bs≡₁) (mk&ₚ{bs₂ = bs₂₃} (consIList{bs₂₁} line₂ (consIList{bs₂₂₁}{bs₂₂₂} line₂' lines₂ refl) refl) final₂ bs≡₂) (WellFounded.acc rs) =
    case (‼ proj₁ xs≡×) of λ where
      refl → case ‼ FullLine.unambiguous line₁ line₂ of λ where
        refl → case ((─ sym (++-assoc bs₁₂₁ bs₁₂₂ bs₁₃)) ,′ (─ trans (proj₂ xs≡×) (sym (++-assoc bs₂₂₁ bs₂₂₂ bs₂₃)))) of λ where
          (─ bs≡₁' , ─ bs≡₂') → case ‼ uaWF (mk&ₚ (consIList line₁' lines₁ refl) final₁ bs≡₁') (mk&ₚ (consIList line₂' lines₂ refl) final₂ bs≡₂') (rs _ (s≤s Nat.≤-refl)) of λ where
            refl → case ‼ ≡-unique bs≡₁ bs≡₂ ret (const _) of λ where
              refl → refl
    where
    import Data.Nat.Properties as Nat
    module ≤ = Nat.≤-Reasoning

    @0 xs≡ : bs₁₁ ++ bs₁₂₁ ++ bs₁₂₂ ++ bs₁₃ ≡ bs₂₁ ++ bs₂₂₁ ++ bs₂₂₂ ++ bs₂₃
    xs≡ = begin
      bs₁₁ ++ bs₁₂₁ ++ bs₁₂₂ ++ bs₁₃ ≡⟨ Lemmas.++-assoc₄ bs₁₁ bs₁₂₁ _ _ ⟩
      (bs₁₁ ++ bs₁₂₁ ++ bs₁₂₂) ++ bs₁₃ ≡⟨ sym bs≡₁ ⟩
      xs ≡⟨ bs≡₂ ⟩
      (bs₂₁ ++ bs₂₂₁ ++ bs₂₂₂) ++ bs₂₃ ≡⟨ sym (Lemmas.++-assoc₄ bs₂₁ bs₂₂₁ _ _) ⟩
      _ ∎

    @0 xs≡× : bs₁₁ ≡ bs₂₁ × bs₁₂₁ ++ bs₁₂₂ ++ bs₁₃ ≡ bs₂₂₁ ++ bs₂₂₂ ++ bs₂₃
    xs≡× = Lemmas.length-++-≡ _ _ _ _ xs≡
             (Nat.≤-antisym
               (≤.begin
                 length bs₁₁ ≤.≤⟨ Nat.m≤m+n _ _ ⟩
                 length bs₁₁ + length (drop (length bs₁₁) bs₂₁) ≤.≡⟨ sym (length-++ bs₁₁) ⟩
                 length (bs₁₁ ++ drop (length bs₁₁) bs₂₁) ≤.≡⟨ cong length {y = bs₂₁} (sym (noOverlapBoundary₁ FullLine.nooverlap (sym xs≡) line₂ line₂' line₁)) ⟩
                 length bs₂₁ ≤.∎)
               (≤.begin
                 length bs₂₁ ≤.≤⟨ Nat.m≤m+n _ _ ⟩
                 length bs₂₁ + length (drop (length bs₂₁) bs₁₁) ≤.≡⟨ sym (length-++ bs₂₁) ⟩
                 length (bs₂₁ ++ drop (length bs₂₁) bs₁₁) ≤.≡⟨ cong length {y = bs₁₁} (sym (noOverlapBoundary₁ FullLine.nooverlap xs≡ line₁ line₁' line₂)) ⟩
                 length bs₁₁ ≤.∎))


