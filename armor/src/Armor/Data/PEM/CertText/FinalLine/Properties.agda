open import Armor.Binary
  renaming (module Base64 to B64)
open import Armor.Data.Base64
open import Armor.Data.PEM.CertText.FinalLine.TCB
open import Armor.Data.PEM.CertText.FullLine.TCB
open import Armor.Data.PEM.RFC5234.TCB
import      Armor.Data.PEM.RFC5234.Properties as RFC5234
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Parallel
import      Armor.Grammar.Seq
import      Armor.Grammar.Sum
open import Armor.Prelude
import      Data.Nat.Properties as Nat
import      Data.List.Relation.Unary.Any.Properties as Any
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.PEM.CertText.FinalLine.Properties where

open  Armor.Grammar.Definitions Char
open  Armor.Grammar.IList       Char
open  Armor.Grammar.Seq         Char
open  Armor.Grammar.Sum         UInt8
open  Armor.Grammar.Parallel    Char

Rep : @0 List Char → Set
Rep = Σₚ (&ₚ Base64Str EOL)
         (λ _ x → Erased (InRange 1 64 (length (&ₚᵈ.bs₁ x))))

equiv : Equivalent Rep CertFinalLine
proj₁ equiv (mk×ₚ (mk&ₚ fstₚ₁ sndₚ₂ refl) (─ range)) =
  mkCertFinalLine fstₚ₁ range sndₚ₂ refl
proj₂ equiv (mkCertFinalLine line lineLen eol refl) =
  mk×ₚ (mk&ₚ line eol refl) (─ lineLen)

@0 nonempty : NonEmpty CertFinalLine
nonempty = Iso.nonempty equiv ne
  where
  module ≤ = Nat.≤-Reasoning

  @0 ne : NonEmpty Rep
  ne {xs} (mk×ₚ (mk&ₚ{bs₁}{bs₂} str eol refl) (─ sndₚ₁)) ≡[] = contradiction (cong length ≡[]) (Nat.>⇒≢
    (≤.begin
      1 ≤.≤⟨ proj₁ sndₚ₁ ⟩
      length bs₁ ≤.≤⟨ Nat.m≤m+n (length bs₁) _ ⟩
      length bs₁ + length bs₂ ≤.≡⟨ sym (length-++ bs₁) ⟩
      length (bs₁ ++ bs₂) ≤.∎))

fromCertFullLine : ∀ {@0 bs} → CertFullLine bs → CertFinalLine bs
fromCertFullLine (mkCertFullLine (mk×ₚ line (─ lineLen)) eol refl) =
  mkCertFinalLine
    (Base64.Str.fromExactLength (mk×ₚ line (─ lineLen)))
      (Nat.≤-trans (toWitness{Q = 1 ≤? 64} tt) (Lemmas.≡⇒≤ (sym lineLen))
    , Lemmas.≡⇒≤ lineLen)
    eol refl

@0 char₁ : ∀ {@0 b bs} → CertFinalLine (b ∷ bs) → b ∈ B64.charset
char₁{b} (mkCertFinalLine{l}{e} (mk64Str  nil strLen pad refl) (str> , str<) eol bs≡) =
  Base64.Pad.char₁ (subst₀! Base64Pad (sym $ proj₂ l≡) pad)
  where
  @0 l≡ : Σ[ l' ∈ List Char ] (b ∷ l') ≡ l
  l≡ = caseErased (singleton l refl) ret (const _) of λ where
    (singleton [] refl) → contradiction str> λ ()
    (singleton (x ∷ x₁) refl) → ─ (x₁ , cong (_∷ x₁) (∷-injectiveˡ bs≡))
char₁{b}{bs} (mkCertFinalLine{e = e} (mk64Str{p = p} (consIList{bs₁}{bs₂} (mk64 c c∈ i refl) t refl) strLen pad refl) (str> , str<) eol bs≡) =
  subst₀ (_∈ B64.charset) (sym (∷-injectiveˡ bs≡)) c∈
  where
  open ≡-Reasoning

@0 char∈ : ∀ {@0 b bs} → b ∈ bs → CertFinalLine bs → b ∈ B64.charset ++ String.toList "=\r\n"
char∈ b∈ (mkCertFinalLine{l}{e} line lineLen eol refl) =
  caseErased Any.++⁻ l b∈ ret (const _) of λ where
    (inj₁ x) → ─
      (caseErased Base64.Str.char∈ x line ret (const _) of λ where
        (inj₁ x) → ─ Any.++⁺ˡ x
        (inj₂ refl) → ─ toWitness{Q = _ ∈? _} tt)
    (inj₂ y) → ─ (caseErased RFC5234.EOL.char∈ y eol ret (const _) of λ where
      (inj₁ refl) → ─ toWitness{Q = _ ∈? _} tt
      (inj₂ refl) → ─ (toWitness{Q = _ ∈? _} tt))

@0 lengthRange : ∀ {@0 bs} → CertFinalLine bs → InRange 2 66 (length bs)
lengthRange{bs} (mkCertFinalLine{l}{e} line lineLen eol bs≡) =
    (≤.begin
      2 ≤.≤⟨ Nat.+-mono-≤ (proj₁ lineLen) (proj₁ $ RFC5234.EOL.eolLen eol) ⟩
      length l + length e ≤.≡⟨ sym (length-++ l) ⟩
      length (l ++ e) ≤.≡⟨ cong length (sym bs≡) ⟩
      length bs ≤.∎ )
  , (≤.begin
      (length bs ≤.≡⟨ cong length bs≡ ⟩
      length (l ++ e) ≤.≡⟨ length-++ l ⟩
      length l + length e ≤.≤⟨ Nat.+-mono-≤ (proj₂ lineLen) (proj₂ $ RFC5234.EOL.eolLen eol) ⟩
      66 ≤.∎))
  where
  module ≤ = Nat.≤-Reasoning

noOverlap : NoOverlap CertFinalLine CertFinalLine
noOverlap ws [] ys₁ xs₂ ys₂ ++≡ fi₁ fi₂ = inj₁ refl
noOverlap ws xs₁@(x₁ ∷ xs₁') ys₁ xs₂ ys₂ ++≡
  (mkCertFinalLine {l₁} {e₁} line₁ lineLen₁ eol₁ bs≡₁) (mkCertFinalLine {l₂} {e₂} line₂ lineLen₂ eol₂ bs≡₂) =
  inj₂ noway
  where
  open ≡-Reasoning

  @0 ws++xs₁≡ : l₂ ++ e₂ ++ xs₁ ≡ l₁ ++ e₁
  ws++xs₁≡ =
    l₂ ++ e₂ ++ xs₁ ≡⟨ sym (++-assoc l₂ _ _) ⟩
    (l₂ ++ e₂) ++ xs₁ ≡⟨ cong (_++ xs₁) (sym bs≡₂) ⟩
    ws ++ xs₁ ≡⟨ bs≡₁ ⟩
    l₁ ++ e₁ ∎

  @0 l₂≡l₁ : l₂ ≡ l₁
  l₂≡l₁ =
    noOverlapBoundary₂
      RFC5234.EOL.noOverlap
      RFC5234.EOL.noOverlap
      (trans ws++xs₁≡ (cong (l₁ ++_) (sym (++-identityʳ e₁)))) line₂ eol₂ line₁ eol₁

  @0 e₂++xs₁≡e₁ : e₂ ++ xs₁ ≡ e₁
  e₂++xs₁≡e₁ = Lemmas.++-cancel≡ˡ _ _ l₂≡l₁ ws++xs₁≡

  @0 x₁≡ : x₁ ≡ '\r' ⊎ x₁ ≡ '\n'
  x₁≡ = RFC5234.EOL.char∈ (Any.++⁺ʳ e₂ (here refl)) (subst₀! EOL (sym e₂++xs₁≡e₁) eol₁)

  @0 x₁≢ : x₁ ∉ B64.charset × x₁ ≢ '='
  x₁≢ =
    [_,_]
      (λ where refl → toWitnessFalse{Q = _ ∈? _} tt , λ ())
      (λ where refl → toWitnessFalse{Q = _ ∈? _} tt , λ ())
      x₁≡

  noway : ¬ CertFinalLine xs₂
  noway (mkCertFinalLine{l₃}{e₃} line₃ lineLen₃ eol₃ bs≡₃) =
    ‼ contradiction₂ x₁∈ (proj₁ x₁≢) (proj₂ x₁≢)
    where
    @0 ∃xs₂' : Σ[ xs₂' ∈ List Char ] x₁ ∷ xs₂' ≡ l₃
    ∃xs₂' = caseErased singleton l₃ refl ret (const _) of λ where
      (singleton [] refl) →
        contradiction{P = 0 ≥ 1} (proj₁ lineLen₃) λ ()
      (singleton (x ∷ xs₂') refl) → ─
        (  xs₂'
        , cong (_∷ xs₂') (∷-injectiveˡ
            (‼ trans ++≡ (cong (_++ ys₂) bs≡₃))))

    @0 x₁∈ : x₁ ∈ B64.charset ⊎ x₁ ≡ '='
    x₁∈ = Base64.Str.char∈ (here{xs = proj₁ ∃xs₂'} refl) (subst₀! Base64Str (sym ∘ proj₂ $ ∃xs₂') line₃)

iso   : Iso Rep CertFinalLine
proj₁ iso = equiv
proj₁ (proj₂ iso) (mk×ₚ (mk&ₚ fstₚ₁ sndₚ₂ refl) sndₚ₁) = refl
proj₂ (proj₂ iso) (mkCertFinalLine line lineLen eol refl) = refl

@0 unambiguous : Unambiguous CertFinalLine
unambiguous = Iso.unambiguous iso
  (Parallel.unambiguous
    (Seq.unambiguousNO Base64.Str.unambiguous RFC5234.EOL.unambiguous RFC5234.EOL.noOverlap)
    (λ _ → erased-unique (inRange-unique { A = ℕ } { B = ℕ })))
