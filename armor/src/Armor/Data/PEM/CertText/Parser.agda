open import Armor.Data.Base64
open import Armor.Data.PEM.CertText.Exclusions
open import Armor.Data.PEM.CertText.FinalLine
open import Armor.Data.PEM.CertText.FullLine
open import Armor.Data.PEM.CertText.Properties
open import Armor.Data.PEM.CertText.TCB
open import Armor.Data.PEM.RFC5234
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Seq
open import Armor.Prelude
import      Data.List.Properties as List
import      Data.Nat.Properties as Nat
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.PEM.CertText.Parser where

open Armor.Grammar.Definitions          Char
open Armor.Grammar.IList                Char
open Armor.Grammar.Parallel             Char
open Armor.Grammar.Parser               Char
open Armor.Grammar.Seq                  Char

open ≡-Reasoning
module ≤ = Nat.≤-Reasoning

parseMaxCertText : LogDec.MaximalParser CertText
parseMaxCertText = LogDec.mkMaximalParser help
  where
  help : ∀ xs → Σ _ _
  help xs =
    case LogDec.runMaximalParser
           (parseIListMaxNoOverlap.parseIListMax
             (mkLogged [ "parseMaxCertText: underflow" ] _)
             _ FullLine.nonempty FullLine.nooverlap parseCertFullLine)
           xs
      ret (const _) of λ where
      (mkLogged _ (no ¬p) , _) →
        contradiction (success _ _ refl nil _ refl) ¬p
      (mkLogged log₁ (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁)) , max₁) →
        case LogDec.runMaximalParser parseCertFinalLine suf₁ of λ where
          (mkLogged log₂ (yes (success pre₂ r₂ r₂≡ v₂ suf₂ ps≡₂)) , max₂) →
            let
              r₁+r₂≡ : Erased (r₁ + r₂ ≡ length pre₁ + length pre₂)
              r₁+r₂≡ = ─ cong₂ _+_ r₁≡ r₂≡
            in
            mkLogged (log₁ ++ log₂)
              (yes
                (success (pre₁ ++ pre₂) (r₁ + r₂)
                  (trans (¡ r₁+r₂≡) (sym (length-++ pre₁)))
                  (mkCertText v₁ v₂ refl) suf₂
                  ((pre₁ ++ pre₂) ++ suf₂ ≡⟨ ++-assoc pre₁ _ _ ⟩
                  pre₁ ++ pre₂ ++ suf₂ ≡⟨ cong (pre₁ ++_) ps≡₂ ⟩
                  pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                  xs ∎)))
            , λ where
              pre' suf' ps≡' (mkCertText{b}{f} body final bs≡) →
                let xs≡ : Erased (b ++ f ++ suf' ≡ pre₁ ++ pre₂ ++ suf₂)
                    xs≡ = ─ (begin (b ++ f ++ suf' ≡⟨ solve (++-monoid Char) ⟩
                                   (b ++ f) ++ suf' ≡⟨ (cong (_++ suf') ∘ sym $ bs≡) ⟩
                                   pre' ++ suf' ≡⟨ ps≡' ⟩
                                   xs ≡⟨ sym ps≡₁ ⟩
                                   pre₁ ++ suf₁ ≡⟨ cong (pre₁ ++_) (sym ps≡₂) ⟩
                                   pre₁ ++ pre₂ ++ suf₂ ∎))
                in
                  uneraseDec
                    (caseErased (Nat.<-cmp (length b) r₁) ret (const _) of λ where
                      (tri> b₁≮ _ b₁>) → ─
                        (contradiction b₁> (Nat.≤⇒≯
                          (max₁ _ (f ++ suf')
                            (begin (b ++ f ++ suf' ≡⟨ solve (++-monoid Char) ⟩
                                   (b ++ f) ++ suf' ≡⟨ cong (_++ suf') (sym bs≡) ⟩
                                   pre' ++ suf' ≡⟨ ps≡' ⟩
                                   xs ∎))
                            body)))
                      (tri≈ _ b≡ _) →
                        let pre₁≡ : Erased (pre₁ ≡ b)
                            pre₁≡ = ─ proj₁ (Lemmas.length-++-≡ _ (pre₂ ++ suf₂) _ (f ++ suf')
                                               (sym (¡ xs≡) )
                                               (trans (sym r₁≡) (sym b≡)))
                        in
                        ─ (Nat.≤-Reasoning.begin length pre' Nat.≤-Reasoning.≡⟨ cong length bs≡ ⟩
                                                 length (b ++ f) Nat.≤-Reasoning.≡⟨ length-++ b ⟩
                                                 length b + length f
                                                   Nat.≤-Reasoning.≤⟨
                                                     Nat.+-mono-≤ (Lemmas.≡⇒≤ b≡)
                                                       (max₂ _ suf'
                                                         (Lemmas.++-cancel≡ˡ _ _
                                                           (sym (¡ pre₁≡)) (trans (¡ xs≡) (cong (pre₁ ++_) ps≡₂)))
                                                         final)
                                                   ⟩
                                                 r₁ + r₂ Nat.≤-Reasoning.∎)
                      (tri< b< _ _) → ─
                        (≤.begin
                          (length pre' ≤.≡⟨ cong length bs≡ ⟩
                          length (b ++ f) ≤.≡⟨ length-++ b ⟩
                          length b + length f
                            ≤.≤⟨
                              body< body final v₁ v₂ (¡ xs≡) (Nat.≤-trans b< (Lemmas.≡⇒≤ r₁≡))
                            ⟩
                          length pre₁ + length pre₂ ≤.≡⟨ sym (¡ r₁+r₂≡) ⟩
                          r₁ + r₂ ≤.∎))

                    )
                    (_ ≤? _)
          (mkLogged log₂ (no ¬p) , snd) →
            case finalLineFromLines v₁ ret (const _) of λ where
              (inj₁ (─ refl)) →
                  (mkLogged (log₁ ++ log₂) (no (λ where
                    (success prefix read read≡ (mkCertText{b}{f} body final refl) suffix ps≡) →
                      let
                        b≡[] : Erased (b ≡ [])
                        b≡[] = ─
                          (caseErased
                            _,_{A = List Char}{B = (_≡ 0) ∘ length} b
                              (Nat.n≤0⇒n≡0
                                (Nat.≤-trans
                                  (max₁ b (f ++ suffix) (trans (sym (++-assoc b f suffix)) ps≡) body)
                                  (Lemmas.≡⇒≤ r₁≡)))
                           ret ((_≡ []) ∘ proj₁) of λ where
                          ([] , snd) → ─ refl)
                      in
                      contradiction
                        (success _ _ refl final suffix
                          (Lemmas.++-cancel≡ˡ _ _ (¡ b≡[])
                            (b ++ f ++ suffix ≡⟨ solve (++-monoid Char) ⟩
                            (b ++ f) ++ suffix ≡⟨ ps≡ ⟩
                            xs ≡⟨ sym ps≡₁ ⟩
                            suf₁ ∎)))
                        ¬p)))
                , tt
              (inj₂ (mk&ₚ{pre₁₁}{pre₁₂} fstₚ₁ (mk×ₚ sndₚ₁ sndₚ₁') bs≡₁₂)) →
                  mkLogged [] (yes
                    (success pre₁ _ r₁≡ (mkCertText fstₚ₁ sndₚ₁ bs≡₁₂) suf₁ ps≡₁))
                , λ where
                  pre' suf' ps≡' (mkCertText{b}{f} body final bs≡) →
                    let
                      bs≡' = ─
                        (b ++ f ++ suf' ≡⟨ solve (++-monoid Char) ⟩
                         (b ++ f) ++ suf' ≡⟨ cong (_++ suf') (sym bs≡) ⟩
                         pre' ++ suf' ≡⟨ ps≡' ⟩
                         xs ∎)

                      bs≡“ : Erased (b ++ f ++ suf' ≡ pre₁₁ ++ pre₁₂ ++ suf₁)
                      bs≡“ = ─ trans (¡ bs≡') (trans (sym ps≡₁) (trans (cong (_++ suf₁) bs≡₁₂) (++-assoc pre₁₁ _ _)))

                      b≤ : Erased (length b ≤ length pre₁)
                      b≤ = ─ Nat.≤-trans
                             (max₁ _ _ (¡ bs≡') body)
                             (Lemmas.≡⇒≤ r₁≡)

                      b< : Erased (length b < length pre₁)
                      b< = ─ Nat.≤∧≢⇒< (¡ b≤) (λ b≡ →
                        let suf₁≡ : f ++ suf' ≡ suf₁
                            suf₁≡ = proj₂
                              (Lemmas.length-++-≡ b (f ++ suf') pre₁ suf₁
                                (b ++ f ++ suf' ≡⟨ ¡ bs≡“ ⟩
                                pre₁₁ ++ pre₁₂ ++ suf₁ ≡⟨ sym (++-assoc pre₁₁ _ _) ⟩
                                (pre₁₁ ++ pre₁₂) ++ suf₁ ≡⟨ cong (_++ suf₁) (sym bs≡₁₂) ⟩
                                pre₁ ++ suf₁ ∎)
                                b≡)
                        in
                        contradiction (success _ _ refl final suf' suf₁≡) ¬p)

                      pf : Erased (length b + length f ≤ length pre₁₁ + length pre₁₂)
                      pf = ─ Nat.≮⇒≥ λ pre₁< →
                        caseErased Nat.<-cmp (length pre₁₁) (length b) ret (const _) of λ where
                          (tri< pre₁₁< _ _) → ─
                            let b≡ : ∃ λ n → b ≡ pre₁₁ ++ pre₁₂ ++ take n suf₁
                                b≡ = foldFinalIntoBody fstₚ₁ sndₚ₁ body final (sym (¡ bs≡“))
                                       pre₁₁<
  
                                n = proj₁ b≡
                            in
                            contradiction
                              (≤.begin
                                length pre₁ ≤.≡⟨ cong length bs≡₁₂ ⟩
                                length (pre₁₁ ++ pre₁₂) ≤.≤⟨ Nat.m≤m+n (length (pre₁₁ ++ pre₁₂)) _ ⟩
                                length (pre₁₁ ++ pre₁₂) + length (take n suf₁) ≤.≡⟨ sym (length-++ (pre₁₁ ++ pre₁₂)) ⟩
                                length ((pre₁₁ ++ pre₁₂) ++ take n suf₁) ≤.≡⟨ cong length (++-assoc pre₁₁ _ _) ⟩
                                length (pre₁₁ ++ pre₁₂ ++ take n suf₁) ≤.≡⟨ cong length (sym (proj₂ b≡)) ⟩
                                length b ≤.∎)
                              (Nat.<⇒≱ (¡ b<))
                          (tri≈ _ pre₁₁≡ _) → ─
                            let b≡× : b ≡ pre₁₁ × f ++ suf' ≡ pre₁₂ ++ suf₁
                                b≡× = Lemmas.length-++-≡ _ _ _ _ (¡ bs≡“) (sym pre₁₁≡)

                                final' : CertFullLine f
                                final' = fullLineFromLine final sndₚ₁' (proj₂ b≡×)

                                b++f≤ : length (b ++ f) ≤ length pre₁
                                b++f≤ = ≤.begin
                                  (length (b ++ f)
                                    ≤.≤⟨ max₁ (b ++ f) suf'
                                           ((b ++ f) ++ suf' ≡⟨ cong (_++ suf') (sym bs≡) ⟩
                                           pre' ++ suf' ≡⟨ ps≡' ⟩
                                           xs ∎)
                                           (appendIList body (consIList final' nil (sym (++-identityʳ f))))
                                    ⟩
                                  r₁ ≤.≡⟨ r₁≡ ⟩
                                  length pre₁ ≤.∎)
                            in
                            contradiction
                              (≤.begin
                                (length b + length f ≤.≡⟨ sym (length-++ b) ⟩
                                length (b ++ f) ≤.≤⟨ b++f≤ ⟩
                                length pre₁ ≤.≡⟨ cong length bs≡₁₂ ⟩
                                length (pre₁₁ ++ pre₁₂) ≤.≡⟨ length-++ pre₁₁ ⟩
                                length pre₁₁ + length pre₁₂ ≤.∎))
                              (Nat.<⇒≱ pre₁<)
                          (tri> _ _ pre₁₁>) → ─
                            let pre₁₁≡ : ∃ λ n → pre₁₁ ≡ b ++ f ++ take n suf'
                                pre₁₁≡ = foldFinalIntoBody body final fstₚ₁ sndₚ₁ (¡ bs≡“) pre₁₁>

                                n = proj₁ pre₁₁≡
                            in
                            contradiction{P = length pre₁₁ + length pre₁₂ < length b + length f}
                              pre₁<
                              (Nat.≤⇒≯ (≤.begin
                                length b + length f ≤.≤⟨ Nat.m≤m+n (length b + length f) _ ⟩
                                length b + length f + length (take n suf') ≤.≡⟨ cong (_+ length (take n suf')) (sym (length-++ b)) ⟩
                                length (b ++ f) + length (take n suf') ≤.≡⟨ sym (length-++ (b ++ f)) ⟩
                                length ((b ++ f) ++ take n suf') ≤.≡⟨ cong length (++-assoc b f _) ⟩
                                length (b ++ f ++ take n suf') ≤.≡⟨ cong length (sym (proj₂ pre₁₁≡)) ⟩
                                length pre₁₁ ≤.≤⟨ Nat.m≤m+n (length pre₁₁) _ ⟩
                                length pre₁₁ + length pre₁₂ ≤.∎))
                    in
                    uneraseDec
                      (subst₂ _≤_
                        (length b + length f ≡⟨ sym (length-++ b) ⟩
                        length (b ++ f) ≡⟨ cong length (sym bs≡) ⟩
                        length pre' ∎)
                        (length pre₁₁ + length pre₁₂ ≡⟨ sym (length-++ pre₁₁) ⟩
                        length (pre₁₁ ++ pre₁₂) ≡⟨ cong length (sym bs≡₁₂) ⟩
                        length pre₁ ≡⟨ sym r₁≡ ⟩
                        r₁ ∎)
                        (¡ pf))
                      (_ ≤? _)
