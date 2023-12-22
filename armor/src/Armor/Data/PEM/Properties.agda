open import Armor.Binary
  renaming (module Base64 to B64)
open import Armor.Data.Base64
open import Armor.Data.PEM.CertBoundary
open import Armor.Data.PEM.CertText
open import Armor.Data.PEM.CertText.FinalLine
open import Armor.Data.PEM.CertText.FullLine
open import Armor.Data.PEM.RFC5234
open import Armor.Data.PEM.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Seq
open import Armor.Prelude
import      Data.List.Relation.Unary.Any.Properties as Any
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.PEM.Properties where

open Armor.Grammar.Definitions          Char
open Armor.Grammar.IList                Char
open Armor.Grammar.Seq                  Char

Rep : @0 List Char → Set
Rep = &ₚ CertHeader (&ₚ CertText CertFooter)

equiv : Equivalent Rep Cert
proj₁ equiv (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) =
  mkCert fstₚ₁ fstₚ₂ sndₚ₁ refl
proj₂ equiv (mkCert header body footer refl) =
  mk&ₚ header (mk&ₚ body footer refl) refl

iso : Iso Rep Cert
proj₁ iso = equiv
proj₁ (proj₂ iso) (mk&ₚ h (mk&ₚ b f refl) refl) = refl
proj₂ (proj₂ iso) (mkCert h b f refl) = refl

nonempty : NonEmpty Cert
nonempty (mkCert (mkCertBoundary refl eol refl) body footer ()) refl

@0 noOverlapHeaderText : NoOverlap CertHeader (&ₚ CertText CertFooter)
noOverlapHeaderText ws [] ys₁ xs₂ ys₂ ++≡ x₁ x₂ = inj₁ refl
noOverlapHeaderText ws xs₁@(x₁ ∷ xs₁') ys₁ xs₂ ys₂ ++≡
  (mkCertBoundary{b}{e} begin eol bs≡) (mkCertBoundary{b₁}{e₁} begin₁ eol₁ bs≡₁) =
  inj₂ noway
  where
  open ≡-Reasoning

  @0 b≡ : b ≡ b₁
  b≡ = trans begin (sym begin₁)

  @0 ++≡w : e₁ ++ xs₁ ≡ e
  ++≡w = ++-cancelˡ b
    (b ++ e₁ ++ xs₁ ≡⟨ cong (_++ e₁ ++ xs₁) b≡ ⟩
    b₁ ++ e₁ ++ xs₁ ≡⟨ sym (++-assoc b₁ e₁ xs₁) ⟩
    (b₁ ++ e₁) ++ xs₁ ≡⟨ cong (_++ xs₁) (sym bs≡₁) ⟩
    ws ++ xs₁ ≡⟨ bs≡ ⟩
    b ++ e ∎)

  @0 x₁≡ : x₁ ≡ '\n'
  x₁≡ = caseErased eol ,′ eol₁ ret (const _) of λ where
    (crlf , crlf) → contradiction ++≡w (λ ())
    (crlf , cr) → ─ (∷-injectiveˡ (∷-injectiveʳ ++≡w))
    (crlf , lf) → contradiction ++≡w λ ()
    (cr , crlf) → contradiction ++≡w λ ()
    (cr , cr) → contradiction ++≡w λ ()
    (cr , lf) → contradiction ++≡w λ ()
    (lf , crlf) → contradiction ++≡w λ ()
    (lf , cr) → contradiction ++≡w λ ()
    (lf , lf) → contradiction ++≡w λ ()

  noway : ¬ &ₚ CertText CertFooter xs₂
  noway (mk&ₚ (mkCertText{f = f} nil final refl) sndₚ₁ bs≡) =
    contradiction x₁∈ (subst₀ (_∉ B64.charset) (sym x₁≡) (toWitnessFalse{Q = _ ∈? _} tt))
    where
    @0 bs₂≡ : ∃ λ xs₂' → x₁ ∷ xs₂' ≡ f
    bs₂≡ = caseErased (singleton f refl) ret (const _) of λ where
      (singleton [] refl) →
        contradiction{P = 2 ≤ 0}
          (proj₁ $ FinalLine.lengthRange final)
          λ ()
      (singleton (x ∷ xs₂') refl) →
        ─ (xs₂'
          , cong (_∷ xs₂')
              (∷-injectiveˡ
                (xs₁ ++ ys₁ ≡⟨ ++≡ ⟩
                 xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡ ⟩
                 _ ∎)))

    @0 x₁∈ : x₁ ∈ B64.charset
    x₁∈ = FinalLine.char₁ (subst₀! CertFinalLine (sym $ proj₂ bs₂≡) final)
  noway (mk&ₚ (mkCertText (consIList{f₁}{b₁} full₁ body refl) final refl) sndₚ₁ bs≡) =
    contradiction x₁∈
      (subst₀ (_∉ B64.charset) (sym x₁≡) (toWitnessFalse{Q = _ ∈? _} tt))
    where
    @0 f₁≡ : ∃ λ f₁' → x₁ ∷ f₁' ≡ f₁
    f₁≡ = caseErased (singleton f₁ refl) ret (const _) of λ where
      (singleton [] refl) →
        contradiction{P = 65 ≤ 0}
          (proj₁ (FullLine.fullLineLen full₁))
          (λ ())
      (singleton (x ∷ f₁') refl) → ─
        (f₁' , (cong (_∷ f₁') (∷-injectiveˡ
          (xs₁ ++ ys₁ ≡⟨ ++≡ ⟩
          xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡ ⟩
          _ ∎))))

    @0 x₁∈ : x₁ ∈ B64.charset
    x₁∈ = FullLine.char₁ (subst₀! CertFullLine (sym (proj₂ f₁≡)) full₁)

noOverlapTextFooter : NoOverlap CertText CertFooter
noOverlapTextFooter ws [] ys₁ xs₂ ys₂ x x₁ x₂ = inj₁ refl
noOverlapTextFooter ws xs₁@(x₁ ∷ xs₁') ys₁ xs₂ ys₂ ++≡
  text₁@(mkCertText{b₁}{f₁} body₁ final₁ bs≡₁)
  text₂@(mkCertText{b₂}{f₂} body₂ final₂ bs≡₂) =
  inj₂ noway
  where
  open ≡-Reasoning

  @0 x₁∈ : x₁ ∈ B64.charset ++ String.toList "=\r\n"
  x₁∈ =
    caseErased
      Any.++⁻ b₁{f₁}
        (subst₀ (x₁ ∈_) bs≡₁ (Any.++⁺ʳ{P = x₁ ≡_} ws {ys = x₁ ∷ xs₁'} (here refl)))
    ret (const _)
    of λ where
      (inj₁ x) → ─ FullLine.char∈List x body₁
      (inj₂ y) → ─ FinalLine.char∈ y final₁

  noway : ¬ CertFooter xs₂
  noway (mkCertBoundary{e = e'} refl eol bs≡) =
    contradiction{P = '-' ∈ B64.charset ++ String.toList "=\r\n"}
      (subst₀ (_∈ B64.charset ++ String.toList "=\r\n") x₁≡' x₁∈)
      (toWitnessFalse{Q = _ ∈? _} tt)
    where
    @0 x₁≡' : x₁ ≡ '-'
    x₁≡' = ∷-injectiveˡ
      (x₁ ∷ xs₁' ++ ys₁ ≡⟨ ++≡ ⟩
       xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡ ⟩
       (_ ++ e') ++ ys₂ ∎)

noOverlap : NoOverlap Cert Cert
noOverlap ws [] ys₁ xs₂ ys₂ ++≡ (mkCert{h₁}{b₁}{f₁} header₁ body₁ footer₁ bs≡₁) (mkCert{h₂}{b₂}{f₂} header₂ body₂ footer₂ bs≡₂) = inj₁ refl
noOverlap ws xs₁@(x₁ ∷ xs₁') ys₁ xs₂ ys₂ ++≡ (mkCert{h₁}{b₁}{f₁} header₁ body₁ footer₁ bs≡₁) (mkCert{h₂}{b₂}{f₂} header₂ body₂ footer₂ bs≡₂) =
  inj₂ noway
  where
  open ≡-Reasoning

  @0 ++≡' : h₁ ++ (b₁ ++ f₁) ++ ys₁ ≡ h₂ ++ (b₂ ++ f₂) ++ xs₂ ++ ys₂
  ++≡' = begin
    (h₁ ++ (b₁ ++ f₁) ++ ys₁ ≡⟨ solve (++-monoid Char) ⟩
    (h₁ ++ b₁ ++ f₁) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡₁) ⟩
    (ws ++ xs₁) ++ ys₁ ≡⟨ ++-assoc ws xs₁ _ ⟩
    ws ++ xs₁ ++ ys₁ ≡⟨ cong (ws ++_) ++≡ ⟩
    ws ++ xs₂ ++ ys₂ ≡⟨ cong (_++ xs₂ ++ ys₂) bs≡₂ ⟩
    (h₂ ++ b₂ ++ f₂) ++ xs₂ ++ ys₂ ≡⟨ solve (++-monoid Char) ⟩
    _ ∎)

  @0 h₁≡ : h₁ ≡ h₂
  h₁≡ =
    noOverlapBoundary₂
      noOverlapHeaderText noOverlapHeaderText
      ++≡'
      header₁ (mk&ₚ body₁ footer₁ refl)
      header₂ (mk&ₚ body₂ footer₂ refl)

  @0 ++≡ₕ : b₁ ++ f₁ ++ ys₁ ≡ b₂ ++ f₂ ++ xs₂ ++ ys₂
  ++≡ₕ = Lemmas.++-cancel≡ˡ _ _ h₁≡
    (h₁ ++ b₁ ++ f₁ ++ ys₁ ≡⟨ solve (++-monoid Char) ⟩
    _ ≡⟨ ++≡' ⟩
    h₂ ++ (b₂ ++ f₂) ++ xs₂ ++ ys₂ ≡⟨ solve (++-monoid Char) ⟩
    _ ∎)

  @0 b₁≡ : b₁ ≡ b₂
  b₁≡ = noOverlapBoundary₂
          noOverlapTextFooter noOverlapTextFooter
          ++≡ₕ
          body₁ footer₁ body₂ footer₂

  @0 ++≡b : f₁ ++ ys₁ ≡ f₂ ++ xs₂ ++ ys₂
  ++≡b = Lemmas.++-cancel≡ˡ _ _ b₁≡ ++≡ₕ

  @0 ++xs₁≡ : f₂ ++ xs₁ ≡ f₁
  ++xs₁≡ =
    Lemmas.++-cancel≡ˡ (h₂ ++ b₂) (h₁ ++ b₁)
      (cong₂ _++_ (sym h₁≡) (sym b₁≡))
      ((h₂ ++ b₂) ++ f₂ ++ xs₁ ≡⟨ sym (++-assoc (h₂ ++ b₂) f₂ _) ⟩
      ((h₂ ++ b₂) ++ f₂) ++ xs₁ ≡⟨ cong (_++ xs₁) (++-assoc h₂ _ _) ⟩
      (h₂ ++ b₂ ++ f₂) ++ xs₁ ≡⟨ cong (_++ xs₁) (sym bs≡₂) ⟩
      ws ++ xs₁ ≡⟨ bs≡₁ ⟩
      h₁ ++ b₁ ++ f₁ ≡⟨ sym (++-assoc h₁ _ _) ⟩
      (h₁ ++ b₁) ++ f₁ ∎)

  @0 x₁≡n : x₁ ≡ '\n'
  x₁≡n = caseErased footer₁ ,′ footer₂ ret (const _) of λ where
    (mkCertBoundary{e = e₁} refl eol₁ refl , mkCertBoundary{e = e₂} refl eol₂ refl) → ─
      let e₂≡ : e₂ ++ xs₁ ≡ e₁
          e₂≡ = ++-cancelˡ _ ++xs₁≡
      in
      caseErased eol₁ ,′ eol₂ ret (const _) of λ where
        (crlf , crlf) → contradiction e₂≡ λ ()
        (crlf , cr) → ─ ∷-injectiveˡ (∷-injectiveʳ e₂≡)
        (crlf , lf) → contradiction e₂≡ λ ()
        (cr , crlf) → contradiction e₂≡ λ ()
        (cr , cr) → contradiction e₂≡ λ ()
        (cr , lf) → contradiction e₂≡ λ ()
        (lf , crlf) → contradiction e₂≡ λ ()
        (lf , cr) → contradiction e₂≡ λ ()
        (lf , lf) → contradiction e₂≡ λ ()
      -- ∷-injectiveˡ{xs = xs₁'}{ys = []}
      --   (++-cancelˡ (String.toList "-----END CERTIFICATE-----")
      --     {!!})

  noway : ¬ Cert xs₂
  noway (mkCert{b'}{f'} (mkCertBoundary refl eol refl) body footer bs≡) =
    contradiction{P = '-' ≡ '\n'} (trans (sym x₁≡) x₁≡n) λ ()
    where
    @0 x₁≡ : x₁ ≡ '-'
    x₁≡ = ∷-injectiveˡ (trans ++≡ (cong (_++ ys₂) bs≡))

@0 unambiguous : Unambiguous Cert
unambiguous = Iso.unambiguous iso
  (Seq.unambiguousNO (CertBoundary.unambiguous _)
  (Seq.unambiguousNO CertText.unambiguous
                     (CertBoundary.unambiguous _)
    noOverlapTextFooter) noOverlapHeaderText)

@0 unambiguousCertList : Unambiguous CertList
unambiguousCertList = IList.unambiguousNO unambiguous nonempty noOverlap 
