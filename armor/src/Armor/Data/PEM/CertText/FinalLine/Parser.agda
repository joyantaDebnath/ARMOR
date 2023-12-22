open import Armor.Data.Base64
open import Armor.Data.PEM.CertText.FinalLine.Properties
open import Armor.Data.PEM.CertText.FinalLine.TCB
open import Armor.Data.PEM.CertText.FullLine.TCB
open import Armor.Data.PEM.RFC5234
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Seq.Properties
import      Armor.Grammar.Seq.TCB
import      Armor.Grammar.Seq.MaximalParser
open import Armor.Prelude
import      Data.Nat.Properties as Nat
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.PEM.CertText.FinalLine.Parser where

open Armor.Grammar.Definitions Char
open Armor.Grammar.IList       Char
open Armor.Grammar.Parallel    Char
open Armor.Grammar.Parser      Char
open Armor.Grammar.Seq.TCB     Char
open Armor.Grammar.Seq.MaximalParser Char

private
  module Seq = Armor.Grammar.Seq.Properties Char

parseCertFinalLine : LogDec.MaximalParser CertFinalLine
parseCertFinalLine =
  LogDec.equivalent equiv (LogDec.mkMaximalParser help)
  where
  open ≡-Reasoning

  help : ∀ xs → Σ _ _
  help xs =
    case LogDec.runMaximalParser
           (parse& parseMaxBase64Str parseMaxEOL RFC5234.EOL.noOverlap) xs
    of λ where
      (mkLogged log (no ¬p) , max) →
        (mkLogged log (no λ where
          (success prefix read read≡ (mk×ₚ fstₚ₁ sndₚ₁) suffix ps≡) →
            contradiction
              (success prefix _ read≡ fstₚ₁ suffix ps≡)
              ¬p))
        , tt
      (mkLogged log (yes (success pre₁ r₁ r₁≡ v₁@(mk&ₚ{bs₁}{bs₂} str eol refl) suf₁ ps≡₁)) , max₁) →
        let bs₁' : Singleton bs₁
            bs₁' = Base64.Str.serialize str
        in
        case inRange? 1 64 (length (↑ bs₁')) ret (const _) of λ where
          (no ¬p) →
            (mkLogged (log ++ ["parseMaxCertFinalLine: overrun"]) (no λ where
              (success prefix read read≡ (mk×ₚ v₁'@(mk&ₚ{bs₁'}{bs₂'} str' eol' refl) ir) suffix ps≡) → ‼
                let
                  xs≡ : Erased (pre₁ ++ suf₁ ≡ prefix ++ suffix)
                  xs≡ = ─ (begin (pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                                 xs ≡⟨ sym ps≡ ⟩
                                 prefix ++ suffix ∎))

                  xs≡' : Erased (bs₁ ++ bs₂ ++ suf₁ ≡ bs₁' ++ bs₂' ++ suffix)
                  xs≡' = ─ (begin
                    bs₁ ++ bs₂ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
                    (bs₁ ++ bs₂) ++ suf₁ ≡⟨ ¡ xs≡ ⟩
                    (bs₁' ++ bs₂') ++ suffix ≡⟨ solve (++-monoid Char) ⟩
                    bs₁' ++ bs₂' ++ suffix ∎)

                  prefix≤ : Erased (length prefix ≤ r₁)
                  prefix≤ = ─ max₁ _ _ ps≡ v₁'

                  pre₁≡ : Erased (pre₁ ≡ prefix ++ drop (length prefix) pre₁)
                  pre₁≡ = ─ Lemmas.drop-length-≤ prefix suffix _ suf₁ (sym $ ¡ xs≡) (Nat.≤-trans (¡ prefix≤) (Lemmas.≡⇒≤ r₁≡))

                  bs₁'≡ : Erased (bs₁ ≡ bs₁' ++ drop (length bs₁') bs₁)
                  bs₁'≡ = ─ Lemmas.drop-length-≤ bs₁' (bs₂' ++ suffix) _ (bs₂ ++ suf₁)
                              (sym (¡ xs≡'))
                              (caseErased (Nat.<-cmp (length bs₁') (length bs₁)) ret (const _) of λ where
                                (tri< bs₁'< _ _) → ─ Nat.<⇒≤{x = length bs₁'} bs₁'<
                                (tri≈ _ bs₁'≡ _) → ─ Lemmas.≡⇒≤ bs₁'≡
                                (tri> _ _ bs₁'>) →
                                  let bs₁'≡ : Erased (bs₁' ≡ bs₁ ++ drop (length bs₁) bs₁')
                                      bs₁'≡ = ─ (Lemmas.drop-length-≤ bs₁ (bs₂ ++ suf₁) _ (bs₂' ++ suffix) (¡ xs≡') (Nat.<⇒≤ bs₁'>))
                                  in
                                  ─ (caseErased RFC5234.EOL.noOverlap bs₁ (drop (length bs₁) bs₁') (bs₂' ++ suffix) bs₂ suf₁
                                       (++-cancelˡ bs₁ (begin
                                         bs₁ ++ drop (length bs₁) bs₁' ++ bs₂' ++ suffix ≡⟨ solve (++-monoid Char) ⟩
                                         (bs₁ ++ drop (length bs₁) bs₁') ++ bs₂' ++ suffix ≡⟨ cong (_++ _) (sym (¡ bs₁'≡)) ⟩
                                         bs₁' ++ bs₂' ++ suffix ≡⟨ (sym $ ¡ xs≡') ⟩
                                         bs₁ ++ bs₂ ++ suf₁ ∎))
                                       (subst₀! Base64Str (¡ bs₁'≡) str') str
                                     ret (const _) of λ where
                                    (inj₁ x) → ─ contradiction
                                                   (begin (length bs₁ ≡⟨ cong length (sym $ ++-identityʳ bs₁) ⟩
                                                          length (bs₁ ++ []) ≡⟨ cong (λ x → length (bs₁ ++ x)) (sym x) ⟩
                                                          length (bs₁ ++ drop (length bs₁) bs₁') ≡⟨ cong length $ sym (¡ bs₁'≡) ⟩
                                                          length bs₁' ∎))
                                                   (Nat.<⇒≢ bs₁'>)
                                    (inj₂ y) → ─ contradiction eol y))
                in
                case
                  RFC5234.EOL.noOverlap _ _ (bs₂ ++ suf₁) bs₂' suffix
                    (++-cancelˡ bs₁' (begin
                      bs₁' ++ drop (length bs₁') bs₁ ++ bs₂ ++ suf₁ ≡⟨ solve (++-monoid Char) ⟩
                      (bs₁' ++ drop (length bs₁') bs₁) ++ bs₂ ++ suf₁ ≡⟨ cong (_++ _) (sym (¡ bs₁'≡)) ⟩
                      bs₁ ++ bs₂ ++ suf₁ ≡⟨ ¡ xs≡' ⟩
                      bs₁' ++ bs₂' ++ suffix ∎))
                    (subst₀! Base64Str (¡ bs₁'≡) str) str'
                ret (const _) of λ where
                  (inj₁ x) → contradiction
                               (subst (InRange 1 64 ∘ length)
                                 (bs₁' ≡ ↑ Base64.Str.serialize str ∋ (begin
                                   (bs₁' ≡⟨ sym (++-identityʳ bs₁') ⟩
                                   bs₁' ++ [] ≡⟨ cong (bs₁' ++_) (sym x) ⟩
                                   bs₁' ++ drop (length bs₁') bs₁ ≡⟨ sym (¡ bs₁'≡) ⟩
                                   bs₁ ≡⟨ (sym ∘ Singleton.x≡ ∘ Base64.Str.serialize $ str) ⟩
                                   ↑ Base64.Str.serialize str ∎)))
                                 (¡ ir))
                               ¬p
                  (inj₂ y) → contradiction eol' y))
            , tt
          (yes p) →
            let ir : Erased (InRange 1 64 (length bs₁))
                ir = ─ subst (InRange 1 64 ∘ length) (Singleton.x≡ bs₁') p
            in
            (mkLogged log (yes
              (success pre₁ _ r₁≡ (mk×ₚ v₁ ir) suf₁ ps≡₁)))
            , λ where
              pre' suf' ps≡' (mk×ₚ v' _) →
                max₁ _ _ ps≡' v'

