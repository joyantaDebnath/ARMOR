open import Armor.Binary
  renaming (module Base64 to B64)
open import Armor.Data.Base64
open import Armor.Data.PEM.CertText.FullLine.TCB
open import Armor.Data.PEM.RFC5234
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Parallel
import      Armor.Grammar.Seq
open import Armor.Prelude
import      Data.List.Relation.Unary.Any.Properties as Any
import      Data.Nat.Properties as Nat

module Armor.Data.PEM.CertText.FullLine.Properties where

open Armor.Grammar.Definitions Char
open Armor.Grammar.IList       Char
open Armor.Grammar.Parallel    Char
open Armor.Grammar.Seq         Char

Rep = &ₚ (ExactLength (IList Base64Char) 64) EOL

equiv : Equivalent Rep CertFullLine
proj₁ equiv (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkCertFullLine fstₚ₁ sndₚ₁ bs≡
proj₂ equiv (mkCertFullLine line eol bs≡) = mk&ₚ line eol bs≡

iso : Iso Rep CertFullLine
proj₁ iso = equiv
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkCertFullLine line eol bs≡) = refl

nonempty : NonEmpty CertFullLine
nonempty (mkCertFullLine (mk×ₚ (consIList (mk64 c c∈ i refl) t refl) (─ len≡)) eol ()) refl

nooverlap : NoOverlap CertFullLine CertFullLine
nooverlap ws [] ys₁ xs₂ ys₂ xs₁++ys₁≡xs₂++ys₂ f₁ f₂ = inj₁ refl
nooverlap ws xs₁@(x₁ ∷ xs₁') ys₁ xs₂ ys₂ xs₁++ys₁≡xs₂++ys₂
  (mkCertFullLine{l}{e} (mk×ₚ line (─ lineLen)) eol bs≡)
  (mkCertFullLine{l₁}{e₁} (mk×ₚ line₁ (─ lineLen₁)) eol₁ bs≡₁) =
  inj₂ noway
  where
  open ≡-Reasoning

  @0 bs≡' : l₁ ++ e₁ ++ xs₁ ≡ l ++ e
  bs≡' = l₁ ++ e₁ ++ xs₁ ≡⟨ sym (++-assoc l₁ e₁ xs₁) ⟩
         (l₁ ++ e₁) ++ xs₁ ≡⟨ cong (_++ xs₁) (sym bs≡₁) ⟩
         ws ++ xs₁ ≡⟨ bs≡ ⟩
         l ++ e ∎

  @0 l×e≡ : l₁ ≡ l × (e₁ ++ xs₁) ≡ e
  l×e≡ = Lemmas.length-++-≡ _ _ _ _ bs≡'
           (length l₁ ≡⟨ lineLen₁ ⟩
            64 ≡⟨ sym lineLen ⟩
            length l ∎)

  @0 x₁≡ : x₁ ≡ '\r' ⊎ x₁ ≡ '\n'
  x₁≡ = RFC5234.EOL.char∈ (subst₀ (x₁ ∈_) (proj₂ l×e≡) (Any.++⁺ʳ e₁ (here refl))) eol

  @0 x₁∉ : x₁ ∉ B64.charset
  x₁∉ = case x₁≡ ret (const _) of λ where
    (inj₁ refl) → toWitnessFalse{Q = _ ∈? _} tt
    (inj₂ refl) → toWitnessFalse{Q = _ ∈? _} tt

  noway : ¬ CertFullLine xs₂
  noway (mkCertFullLine{l'}{e'} (mk×ₚ line' (─ lineLen')) eol' bs≡“) =
    contradiction l₁'∈ (subst₀ (_∉ B64.charset) l₁'≡ x₁∉)
    where
    abstract
      @0 l'≡ : Σ[ p ∈ Char × List Char ] uncurry _∷_ p ≡ l'
      l'≡ = case singleton l' refl ret (const _) of λ where
        (singleton [] refl) → contradiction lineLen' λ ()
        (singleton (x ∷ x₁) refl) → (x , x₁) , refl

    @0 l₁' : Char
    l₁' = proj₁ (proj₁ l'≡)

    @0 l“ : List Char
    l“  = proj₂ (proj₁ l'≡)

    @0 l₁'≡ : x₁ ≡ l₁'
    l₁'≡ = ∷-injectiveˡ
             (x₁ ∷ xs₁' ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
              xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡“ ⟩
              (l' ++ e') ++ ys₂ ≡⟨ ++-assoc l' e' ys₂ ⟩
              l' ++ e' ++ ys₂ ≡⟨ cong (λ x → x ++ e' ++ ys₂) (sym (proj₂ l'≡)) ⟩
              (l₁' ∷ l“) ++ e' ++ ys₂ ∎)

    @0 l₁'∈ : l₁' ∈ B64.charset
    l₁'∈ = caseErased Base64.Char.iList2All line' ret (const _) of λ where
      (mk64 c c∈ i refl ∷ x) →
        ─ subst₀ (_∈ B64.charset) (∷-injectiveˡ (sym $ proj₂ l'≡)) c∈

@0 fullLineLen : ∀ {@0 bs} → CertFullLine bs → InRange 65 66 (length bs)
fullLineLen{bs} (mkCertFullLine{l}{e} (mk×ₚ line (─ lineLen)) eol bs≡) =
    (≤.begin
      (64 + 1 ≤.≡⟨ cong (_+ 1) (sym lineLen) ⟩
      length l + 1 ≤.≤⟨ Nat.+-monoʳ-≤ (length l) (proj₁ eolLen) ⟩
      length l + length e ≤.≡⟨ sym (length-++ l) ⟩
      length (l ++ e) ≤.≡⟨ cong length (sym bs≡) ⟩
      length bs ≤.∎))
  , (≤.begin
      (length bs ≤.≡⟨ cong length bs≡ ⟩
      length (l ++ e) ≤.≡⟨ length-++ l ⟩
      length l + length e ≤.≤⟨ Nat.+-monoʳ-≤ (length l) (proj₂ eolLen) ⟩
      length l + 2 ≤.≡⟨ cong (_+ 2) lineLen ⟩
      66 ≤.∎))
  where
  module ≤ = Nat.≤-Reasoning
  eolLen = RFC5234.EOL.eolLen eol

@0 char₁ : ∀ {@0 b bs} → CertFullLine (b ∷ bs) → b ∈ B64.charset
char₁ (mkCertFullLine (mk×ₚ (consIList (mk64 c c∈ _ refl) t refl) (─ len≡)) eol bs≡) =
  subst₀ (_∈ B64.charset) (sym (∷-injectiveˡ bs≡)) c∈

@0 char∈ : ∀ {@0 b bs} → b ∈ bs → CertFullLine bs → b ∈ B64.charset ++ (String.toList $ "=\r\n")
char∈ b∈ (mkCertFullLine{l}{e} line eol refl) =
  caseErased Any.++⁻ l b∈ ret (const _) of λ where
    (inj₁ x) → ─ Any.++⁺ˡ{xs = B64.charset ++ [ '=' ]}
      (caseErased Base64.Str.char∈ x (Base64.Str.fromExactLength line) ret (const _) of λ where
        (inj₁ x) → ─ Any.++⁺ˡ x
        (inj₂ refl) → ─ (Any.++⁺ʳ B64.charset (here refl)))
    (inj₂ y) → ─
      (caseErased RFC5234.EOL.char∈ y eol ret (const _) of λ where
        (inj₁ refl) → ─ toWitness{Q = _ ∈? _} tt
        (inj₂ refl) → ─ toWitness{Q = _ ∈? _} tt)

@0 char∈List : ∀ {@0 b bs} → b ∈ bs → IList CertFullLine bs → b ∈ B64.charset ++ (String.toList $ "=\r\n")
char∈List () nil
char∈List b∈ (consIList{l}{r} line lines refl) =
  caseErased Any.++⁻ l b∈ ret (const _) of λ where
    (inj₁ x) → ─ char∈ x line
    (inj₂ y) → ─ char∈List y lines

@0 unambiguous : Unambiguous CertFullLine
unambiguous = Iso.unambiguous iso ua
  where
  @0 ua : Unambiguous Rep
  ua = Seq.unambiguous
         (Parallel.ExactLength.unambiguous _
           (IList.unambiguous Base64.Char.unambiguous Base64.Char.nonempty Base64.Char.nosubstrings))
         (Parallel.ExactLength.nosubstrings _)
         RFC5234.EOL.unambiguous

