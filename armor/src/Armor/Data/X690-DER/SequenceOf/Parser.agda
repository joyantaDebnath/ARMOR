open import Armor.Binary
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.Length
open import Armor.Data.X690-DER.SequenceOf.TCB
open import Armor.Data.X690-DER.SequenceOf.Properties as SequenceOf
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Armor.Data.X690-DER.SequenceOf.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.IList       UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

module parseSequenceOf
  (eName : String) (A : @0 List UInt8 → Set) (@0 ne : NonEmpty A) (@0 nn : NoSubstrings A)
  (p : Parser (Logging ∘ Dec) A) where

  here' = "parseSeq: "

  open ≡-Reasoning
  open import Tactic.MonoidSolver using (solve ; solve-macro)

  parseSequenceOfWF : ∀ n → ParserWF (Logging ∘ Dec) (ExactLength (SequenceOf A) n)
  runParser (parseSequenceOfWF    zero) xs (WellFounded.acc rs) =
    return (yes
      (success [] _ refl (mk×ₚ nil (─ refl)) xs refl))
  runParser (parseSequenceOfWF n@(suc _)) xs (WellFounded.acc rs) = do
    yes (success pre₀ r₀ r₀≡ (mk×ₚ v₀ (─ r₀≤len)) suf₀ ps≡₀)
      ← runParser (parse≤ n p nn (tell $ here' String.++ "overflow")) xs
      where no ¬parse → do
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ nil (─ ())) suffix ps≡)
          (success .(bs₁ ++ bs₂) read read≡ (mk×ₚ (cons (mkSequenceOf{bs₁}{bs₂} h t refl)) (─ bsLen)) suffix ps≡) →
            contradiction
              (success bs₁ _ refl
                (mk×ₚ h (─ m+n≤o⇒m≤o _ {length bs₂} (Lemmas.≡⇒≤ (trans (sym $ length-++ bs₁) bsLen))))
                (bs₂ ++ suffix)
                (begin (bs₁ ++ bs₂ ++ suffix ≡⟨ solve (++-monoid UInt8) ⟩
                        (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡ ⟩
                        xs ∎)))
              ¬parse
    case <-cmp r₀ n of λ where
      (tri> _ _ r₀>n) →
        contradiction (≤-trans (Lemmas.≡⇒≤ r₀≡) r₀≤len) (<⇒≱ r₀>n)
      (tri≈ _ r₀≡n _) →
        return (yes
          (success pre₀ _ r₀≡
            (mk×ₚ (cons (mkSequenceOf v₀ nil (solve (++-monoid UInt8)))) (─ trans (sym r₀≡) r₀≡n)) suf₀ ps≡₀))
      (tri< r₀<n _ _) → do
        let @0 suf₀<xs : length suf₀ < length xs
            suf₀<xs = subst (λ i → length suf₀ < length i) ps≡₀ (Lemmas.length-++-< pre₀ suf₀ (ne v₀))
        yes (success pre₁ r₁ r₁≡ (mk×ₚ v₁ (─ r₁≡len-pre₁)) suf₁ ps≡₁)
          ← runParser (parseSequenceOfWF (n ∸ r₀)) suf₀ (rs _ suf₀<xs)
          where no ¬parse → do
            return ∘ no $ λ where
              (success prefix read read≡ (mk×ₚ nil (─ ())) suffix ps≡)
              (success .(bs₁ ++ bs₂) read read≡ (mk×ₚ (cons (mkSequenceOf{bs₁}{bs₂} h t refl)) (─ bsLen)) suffix ps≡) → ‼
                let @0 xs≡ : pre₀ ++ suf₀ ≡ bs₁ ++ bs₂ ++ suffix
                    xs≡ = begin pre₀ ++ suf₀            ≡⟨ ps≡₀ ⟩
                                 xs                     ≡⟨ sym ps≡ ⟩
                                 (bs₁ ++ bs₂) ++ suffix ≡⟨ solve (++-monoid UInt8) ⟩
                                 bs₁ ++ bs₂ ++ suffix   ∎

                    @0 pre₀≡bs₁ : pre₀ ≡ bs₁
                    pre₀≡bs₁ = nn xs≡ v₀ h
                in
                contradiction
                  (success bs₂ _ refl
                    (mk×ₚ t
                      (─ +-cancelˡ-≡ r₀
                         (begin (r₀ + length bs₂         ≡⟨ cong (_+ length bs₂) r₀≡ ⟩
                                length pre₀ + length bs₂ ≡⟨ cong (λ x → length x + length bs₂) pre₀≡bs₁ ⟩
                                length bs₁ + length bs₂  ≡⟨ sym (length-++ bs₁) ⟩
                                length (bs₁ ++ bs₂)      ≡⟨ bsLen ⟩
                                n                        ≡⟨ sym (+-identityʳ _) ⟩
                                n + 0                    ≡⟨ cong (n +_) (sym (n∸n≡0 r₀)) ⟩
                                n + (r₀ - r₀)            ≡⟨ sym (+-∸-assoc n {r₀} ≤-refl) ⟩
                                (n + r₀) - r₀            ≡⟨ cong (_∸ r₀) (+-comm n _) ⟩
                                (r₀ + n) - r₀            ≡⟨ +-∸-assoc r₀ {n} (<⇒≤ r₀<n) ⟩
                                r₀ + (n - r₀)            ∎))))
                    suffix
                    (++-cancelˡ bs₁ (trans (sym xs≡) (cong (_++ suf₀) pre₀≡bs₁))))
                  ¬parse
        return (yes
          (success (pre₀ ++ pre₁) (r₀ + r₁)
            (begin (r₀ + r₁                   ≡⟨ cong (_+ r₁) r₀≡ ⟩
                    length pre₀ + r₁          ≡⟨ cong (length pre₀ +_) r₁≡ ⟩
                    length pre₀ + length pre₁ ≡⟨ (sym $ length-++ pre₀) ⟩
                    length (pre₀ ++ pre₁)     ∎))
            (mk×ₚ (cons (mkSequenceOf v₀ v₁ refl))
              (─(begin (length (pre₀ ++ pre₁)     ≡⟨ length-++ pre₀ ⟩
                         length pre₀ + length pre₁ ≡⟨ cong (_+ _) (sym r₀≡) ⟩
                         r₀ + length pre₁          ≡⟨ cong (r₀ +_) r₁≡len-pre₁ ⟩
                         r₀ + (n - r₀)             ≡⟨ sym (+-∸-assoc r₀ (<⇒≤ r₀<n)) ⟩
                         r₀ + n - r₀               ≡⟨ cong (_∸ r₀) (+-comm r₀ n) ⟩
                         n + r₀ - r₀               ≡⟨ +-∸-assoc n {n = r₀} ≤-refl ⟩
                         n + (r₀ - r₀)             ≡⟨ cong (n +_) (n∸n≡0 r₀) ⟩
                         n + 0                     ≡⟨ +-identityʳ n ⟩
                         n                         ∎))))
            suf₁
            (begin ((pre₀ ++ pre₁) ++ suf₁  ≡⟨ solve (++-monoid UInt8) ⟩
                    pre₀ ++ pre₁ ++ suf₁    ≡⟨ cong (pre₀ ++_) ps≡₁ ⟩
                    pre₀ ++ suf₀            ≡⟨ ps≡₀ ⟩
                    xs                      ∎))))

  parseSequenceOf : ∀ n → Parser (Logging ∘ Dec) (ExactLength (SequenceOf A) n)
  parseSequenceOf n = parseWF (parseSequenceOfWF n)

  parseBoundedSequenceOf : ∀ n b → Parser (Logging ∘ Dec) (ExactLength (BoundedSequenceOf A b) n)
  runParser (parseBoundedSequenceOf n b) xs = do
    yes (success pre₀ r₀ r₀≡ (mk×ₚ v₀ (─ v₀Len)) suf₀ ps≡₀)
      ← runParser (parseSequenceOf n) xs
      where no ¬parse → do
        return ∘ no $ λ where
          x → contradiction (mapSuccess (λ where (mk×ₚ (mk×ₚ fstₚ₁ sndₚ₂) sndₚ₁) → mk×ₚ fstₚ₁ sndₚ₁) x) ¬parse
    case b ≤? lengthSequence v₀ of λ where
      (yes b≤len) →
        return (yes
          (success pre₀ r₀ r₀≡ (mk×ₚ (mk×ₚ v₀ (─ b≤len)) (─ v₀Len)) suf₀ ps≡₀))
      (no  b≰len) → do
        tell $ here' String.++ eName String.++ ": does not meet min length"
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ (mk×ₚ fstₚ₁ sndₚ₂) (─ sndₚ₁)) suffix ps≡) → ‼
            let @0 pre₀≡ : prefix ≡ pre₀
                pre₀≡ = proj₁ (Lemmas.length-++-≡ _ _ _ _ (trans₀ ps≡ (sym ps≡₀)) (trans₀ sndₚ₁ (sym v₀Len)))

                @0 numElems≡ : lengthSequence fstₚ₁ ≡ lengthSequence v₀
                numElems≡ =
                  trans₀
                    (sameLength nn ne fstₚ₁ (subst₀! (SequenceOf _) (sym pre₀≡) v₀))
                    (≡-elim (λ {ys} eq → (v : SequenceOf _ ys) → lengthSequence (subst₀! _ (sym eq) v) ≡ lengthSequence v)
                      (λ _ → refl) pre₀≡ v₀)
            in
            contradiction
              (subst (b ≤_) numElems≡ (Erased.x sndₚ₂))
              b≰len

  parseSeq : Parser (Logging ∘ Dec) (Seq A)
  parseSeq = parseTLV Tag.Sequence ("parseSeq: " String.++ eName) (SequenceOf A) parseSequenceOf

  parseNonEmptySeq : Parser (Logging ∘ Dec) (NonEmptySeq A)
  parseNonEmptySeq = parseTLV Tag.Sequence ("parseNonEmptySeq: " String.++ eName) (NonEmptySequenceOf A) λ n → parseBoundedSequenceOf n 1

open parseSequenceOf public using (parseSequenceOf ; parseBoundedSequenceOf ; parseNonEmptySeq ; parseSeq)

parseIntegerSeq : Parser (Logging ∘ Dec) IntegerSeq
parseIntegerSeq = parseSeq "int" Int TLV.nonempty TLV.nosubstrings (Int.parse "") -- parseInt

-- private
--   module Test where

--     elm₁ : List UInt8
--     elm₁ = Tag.Integer ∷ # 1 ∷ [ # 4 ]

--     elm₂ : List UInt8
--     elm₂ = Tag.Integer ∷ # 1 ∷ [ # 5 ]

--     elm₃ : List UInt8
--     elm₃ = Tag.Integer ∷ # 1 ∷ [ # 6 ]

--     elm₄ : List UInt8
--     elm₄ = Tag.Boolean ∷ # 1 ∷ [ # 255 ]

--     Seq₁₂₃ : List UInt8
--     Seq₁₂₃ = Tag.Sequence ∷ [ # 9 ] ++ elm₁ ++ elm₂ ++ elm₃

--     Seq₁₂₄ : List UInt8
--     Seq₁₂₄ = Tag.Sequence ∷ [ # 9 ] ++ elm₁ ++ elm₂ ++ elm₄

--     SeqBad₁₂₃ : List UInt8
--     SeqBad₁₂₃ = Tag.Sequence ∷ [ # 19 ] ++ elm₁ ++ elm₂ ++ elm₄

--     test₁ : Seq Int Seq₁₂₃
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser (parseSeq "int" Int Props.TLV.nonempty Props.TLV.nosubstrings parseInt) Seq₁₂₃)} tt)

--     test₂ : IntegerSeq Seq₁₂₃
--     test₂ = Success.value (toWitness {Q = Logging.val (runParser parseIntegerSeq Seq₁₂₃)} tt)

--     test₃ : ¬ Success IntegerSeq Seq₁₂₄
--     test₃ = toWitnessFalse {Q = Logging.val (runParser parseIntegerSeq Seq₁₂₄)} tt

--     test₄ : ¬ Success IntegerSeq SeqBad₁₂₃
--     test₄ = toWitnessFalse {Q = Logging.val (runParser parseIntegerSeq SeqBad₁₂₃)} tt


