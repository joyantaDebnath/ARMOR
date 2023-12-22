open import Armor.Binary
open import Armor.Data.Base64.TCB
open import Armor.Data.Base64.Properties
open import Armor.Prelude
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
import      Data.Nat.Properties as Nat

module Armor.Data.Base64.Parser where

open Armor.Grammar.Definitions Char
open Armor.Grammar.IList       Char
open Armor.Grammar.Parallel    Char
open Armor.Grammar.Parser      Char
open Armor.Grammar.Seq         Char
module Props = Armor.Grammar.Properties Char

module parseBase64 where
  hereChar = "Base64: Char"

  open ≡-Reasoning

  parseBase64Char : Parser (Logging ∘ Dec) Base64Char
  runParser parseBase64Char [] = do
    tell $ hereChar String.++ ": underflow"
    return ∘ no $ λ where
      (success prefix read read≡ (mk64 c c∈ i refl) suffix ())
  runParser parseBase64Char (x ∷ xs) = do
    case x ∈? Base64.charset of λ where
      (no ¬p) → do
        tell $ hereChar String.++ ": invalid char " String.++ String.fromList [ x ]
        return ∘ no $ λ where
          (success prefix read read≡ (mk64 c c∈ i refl) suffix refl) →
            contradiction c∈ ¬p
      (yes c∈) →
        return (yes
          (success [ x ] _ refl (mk64 x c∈ self refl) xs refl))

  parseBase64Pad1 : Parser (Logging ∘ Dec) Base64Pad1
  parseBase64Pad1 =
    parseEquivalent Base64Pad.equiv₁
      (parse& (Seq.nosubstrings Base64Char.nosubstrings Base64Char.nosubstrings)
        (parse& Base64Char.nosubstrings parseBase64Char parseBase64Char)
        (parse&
          (Parallel.nosubstrings₁ Base64Char.nosubstrings)
          (parseSigma Base64Char.nosubstrings Base64Char.unambiguous parseBase64Char
            (λ where (mk64 c c∈ i bs≡) → _ ≟ 0))
          (parseLitE
            (tell $ here' String.++ ": underflow")
            (tell $ here' String.++ ": mismatch") _)))
    where here' = "parseBase64Pad1"

  parseBase64Pad2 : Parser (Logging ∘ Dec) Base64Pad2
  parseBase64Pad2 =
    parseEquivalent Base64Pad.equiv₂
      (parse& Base64Char.nosubstrings parseBase64Char
        (parse& (Parallel.nosubstrings₁ Base64Char.nosubstrings)
          (parseSigma Base64Char.nosubstrings Base64Char.unambiguous
            parseBase64Char
              (λ where (mk64 c c∈ i bs≡) → _ ≟ 0))
          (parseLitE
            (tell $ here' String.++ ": underflow") (tell $ here' String.++ ": mismatch") _)))
    where
    here' = "parseBase64Pad2"

  parseMaxBase64Pad : LogDec.MaximalParser Base64Pad
  parseMaxBase64Pad = LogDec.mkMaximalParser help
    where
    help : ∀ xs → Σ (Logging ∘ Dec $ Success Base64Pad xs) _
    help [] = (mkLogged [] (yes (success [] _ refl (pad0 refl) [] refl)))
              , λ where
                  .[] .[] refl (pad0 refl) → z≤n
                  pre' suf' eq (pad1 (mk64P1{b₁}{b₂}{b₃} c₁ c₂ c₃ pad bs≡)) →
                    contradiction{P = 4 + length suf' ≡ 0}
                      (begin length (b₁ ∷ b₂ ∷ b₃ ∷ [ '=' ]) + length suf' ≡⟨ cong (λ x → length x + length suf') (sym bs≡) ⟩
                             length pre' + length suf'                     ≡⟨ sym (length-++ pre') ⟩
                             length (pre' ++ suf')                         ≡⟨ cong length eq ⟩
                             length{A = Char} []                           ∎)
                      λ ()
                  pre' suf' eq (pad2 (mk64P2{b₁}{b₂} c₁ c₂ pad bs≡)) →
                    contradiction {P = 4 + length suf' ≡ 0}
                      (begin length (b₁ ∷ b₂ ∷ '=' ∷ [ '=' ]) + length suf' ≡⟨ cong (λ x → length x + length suf') (sym bs≡) ⟩
                             length pre' + length suf'                      ≡⟨ sym (length-++ pre') ⟩
                             length (pre' ++ suf')                          ≡⟨ cong length eq ⟩
                             length{A = Char} []                            ∎)
                      λ ()
    help (c₁ ∷ []) =
      (mkLogged [] (yes (success [] _ refl (pad0 refl) [ c₁ ] refl)))
      , λ where
          .[] suf' eq (pad0 refl) → z≤n
          pre' suf' eq (pad1 (mk64P1{b₁}{b₂}{b₃} c₁' c₂' c₃' pad bs≡)) →
            contradiction {P = 4 + length suf' ≡ 1}
              (begin length (b₁ ∷ b₂ ∷ b₃ ∷ [ '=' ]) + length suf' ≡⟨ cong (λ x → length x + length suf') (sym bs≡) ⟩
                             length pre' + length suf'             ≡⟨ sym (length-++ pre') ⟩
                             length (pre' ++ suf')                 ≡⟨ cong length eq ⟩
                             length [ c₁ ]                         ∎)
              (λ ())
          pre' suf' eq (pad2 (mk64P2{b₁}{b₂} c₁ c₂ pad bs≡)) →
            contradiction {P = 4 + length suf' ≡ 1}
              (begin length (b₁ ∷ b₂ ∷ '=' ∷ [ '=' ]) + length suf' ≡⟨ cong (λ x → length x + length suf') (sym bs≡) ⟩
                             length pre' + length suf'              ≡⟨ sym (length-++ pre') ⟩
                             length (pre' ++ suf')                  ≡⟨ cong length eq ⟩
                             length [ c₁ ]                          ∎)
              (λ ())
    help (c₁ ∷ c₂ ∷ []) =
      (mkLogged [] (yes (success [] _ refl (pad0 refl) (c₁ ∷ [ c₂ ]) refl)))
      , λ where
          .[] suf' eq (pad0 refl) → z≤n
          pre' suf' eq (pad1 (mk64P1{b₁}{b₂}{b₃} c₁' c₂' c₃' pad bs≡)) →
            contradiction {P = 4 + length suf' ≡ 2}
              (begin length (b₁ ∷ b₂ ∷ b₃ ∷ [ '=' ]) + length suf' ≡⟨ cong (λ x → length x + length suf') (sym bs≡) ⟩
                             length pre' + length suf'             ≡⟨ sym (length-++ pre') ⟩
                             length (pre' ++ suf')                 ≡⟨ cong length eq ⟩
                             length (c₁ ∷ [ c₂ ])                  ∎)
              (λ ())
          pre' suf' eq (pad2 (mk64P2{b₁}{b₂} c₁' c₂' pad bs≡)) →
            contradiction {P = 4 + length suf' ≡ 2}
              (begin length (b₁ ∷ b₂ ∷ '=' ∷ [ '=' ]) + length suf' ≡⟨ cong (λ x → length x + length suf') (sym bs≡) ⟩
                             length pre' + length suf'              ≡⟨ sym (length-++ pre') ⟩
                             length (pre' ++ suf')                  ≡⟨ cong length eq ⟩
                             length (c₁ ∷ [ c₂ ])                   ∎)
              (λ ())
    help (c₁ ∷ c₂ ∷ c₃ ∷ []) =
      (mkLogged [] (yes (success [] _ refl (pad0 refl) (c₁ ∷ c₂ ∷ [ c₃ ]) refl)))
      , λ where
          .[] suf' eq (pad0 refl) → z≤n
          pre' suf' eq (pad1 (mk64P1{b₁}{b₂}{b₃} c₁' c₂' c₃' pad bs≡)) →
            contradiction {P = 4 + length suf' ≡ 3}
              (begin length (b₁ ∷ b₂ ∷ b₃ ∷ [ '=' ]) + length suf' ≡⟨ cong (λ x → length x + length suf') (sym bs≡) ⟩
                             length pre' + length suf'             ≡⟨ sym (length-++ pre') ⟩
                             length (pre' ++ suf')                 ≡⟨ cong length eq ⟩
                             length (c₁ ∷ c₂ ∷ [ c₃ ])             ∎)
              (λ ())
          pre' suf' eq (pad2 (mk64P2{b₁}{b₂} c₁' c₂' pad bs≡)) →
            contradiction {P = 4 + length suf' ≡ 3}
              (begin length (b₁ ∷ b₂ ∷ '=' ∷ [ '=' ]) + length suf' ≡⟨ cong (λ x → length x + length suf') (sym bs≡) ⟩
                             length pre' + length suf'              ≡⟨ sym (length-++ pre') ⟩
                             length (pre' ++ suf')                  ≡⟨ cong length eq ⟩
                             length (c₁ ∷ c₂ ∷ [ c₃ ])              ∎)
              (λ ())
    help xs'@(c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ xs) =
      let p₁ = runParser parseBase64Pad1 xs'
      in
      case p₁ of λ where
        (mkLogged log (yes (success prefix read read≡ value@(mk64P1 c₁ c₂ c₃ pad refl) suffix ps≡))) →
          (mkLogged log (yes (success prefix _ read≡ (pad1 value) suffix ps≡)))
          , λ where
              .[] suf' eq (pad0 refl) → z≤n
              pre' suf' eq (pad1 (mk64P1 c₁ c₂ c₃ pad bs≡)) →
                Lemmas.≡⇒≤
                  (begin (length pre' ≡⟨ ‼ (cong length bs≡) ⟩
                         4 ≡⟨ ‼ sym read≡ ⟩
                         read ∎))
              pre' suf' eq (pad2 (mk64P2 c₁ c₂ pad bs≡)) →
                Lemmas.≡⇒≤
                  (begin (length pre' ≡⟨ ‼ cong length bs≡ ⟩
                  4 ≡⟨ ‼ sym read≡ ⟩
                  read ∎))
        (mkLogged log (no ¬p₁)) →
          let p₂ = runParser parseBase64Pad2 xs'
          in
          case p₂ of λ where
            (mkLogged log (yes (success pre₁ r₁ r₁≡ v₁@(mk64P2 c₁ c₂ pad refl) suf₁ ps≡₁))) →
              (mkLogged log (yes (success pre₁ _ r₁≡ (pad2 v₁) suf₁ ps≡₁)))
              , λ where
                  .[] suf' eq (pad0 refl) → z≤n
                  pre' suf' eq (pad1 (mk64P1 c₁ c₂ c₃ pad bs≡)) →
                    Lemmas.≡⇒≤
                      (begin (length pre' ≡⟨ cong length (‼ bs≡) ⟩
                             4 ≡⟨ ‼ sym r₁≡ ⟩
                             r₁ ∎))
                  pre' suf' eq (pad2 (mk64P2 c₁ c₂ pad bs≡)) →
                    Lemmas.≡⇒≤ (‼
                      (begin (length pre' ≡⟨ cong length (‼ bs≡) ⟩
                             4 ≡⟨ ‼ (sym r₁≡) ⟩
                             r₁ ∎)))
            (mkLogged log (no ¬p₂)) →
              (mkLogged [ "parseBase64Pad: not pad: " String.++ String.fromList (c₁ ∷ c₂ ∷ c₃ ∷ [ c₄ ])]
                (yes (success [] _ refl (pad0 refl) xs' refl)))
              , λ where
                .[] suf' eq (pad0 refl) → z≤n
                pre' suf' eq (pad1 v@(mk64P1{b₁'}{b₂'}{b₃'} c₁' c₂' c₃' pad bs≡)) →
                  contradiction
                    (success pre' _ refl v suf' eq)
                    ¬p₁
                pre' suf' eq (pad2 v@(mk64P2 c₁ c₂ pad bs≡)) →
                  contradiction
                    (success pre' _ refl v suf' eq)
                    ¬p₂

  parseMaxBase64Str : LogDec.MaximalParser Base64Str
  parseMaxBase64Str =
    LogDec.equivalent Base64Str.equiv
      (parse&o₂
        (parseIListMax (mkLogged ["parseMaxBase64Str: underflow"] tt) _
          (Seq.nonempty₁ Base64Char.nonempty) nn4
          (parse& Base64Char.nosubstrings parseBase64Char
            (parse& Base64Char.nosubstrings parseBase64Char
              (parse& Base64Char.nosubstrings parseBase64Char parseBase64Char))))
        (LogDec.equivalent (Iso.symEquivalent Base64Pad.equiv) parseMaxBase64Pad)
        Base64Str.noOverlap)
    where
    open import Armor.Grammar.Option.MaximalParser Char

    @0 nn4 : NoSubstrings (&ₚ Base64Char (&ₚ Base64Char (&ₚ Base64Char Base64Char)))
    nn4 = Seq.nosubstrings Base64Char.nosubstrings
            (Seq.nosubstrings Base64Char.nosubstrings
              (Seq.nosubstrings Base64Char.nosubstrings Base64Char.nosubstrings))

open parseBase64 public
  using (parseBase64Char; parseMaxBase64Pad; parseMaxBase64Str)
