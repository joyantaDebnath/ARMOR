open import Armor.Binary
open import Armor.Data.Unicode.UTF8.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Parallel
import      Armor.Grammar.Properties
import      Armor.Grammar.Sum
open import Armor.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Relation.Binary
  hiding (NonEmpty)

module Armor.Data.Unicode.UTF8.Properties where

open Armor.Grammar.Definitions              UInt8
open Armor.Grammar.IList                    UInt8
open Armor.Grammar.Parallel                 UInt8
open Armor.Grammar.Properties               UInt8
open Armor.Grammar.Sum                      UInt8

module UTF8Char1Props where
  @0 unambiguous : Unambiguous UTF8Char1
  unambiguous (mkUTF8Char1 b₁ b₁range refl) (mkUTF8Char1 .b₁ b₁range₁ refl) =
    subst (λ b₁range' → _ ≡ mkUTF8Char1 _ b₁range' refl) (≤-unique b₁range b₁range₁) refl

  nosubstrings : NoSubstrings UTF8Char1
  nosubstrings xs₁++ys₁≡xs₂++ys₂ (mkUTF8Char1 b₁ b₁range refl) (mkUTF8Char1 b₂ b₁range₁ refl) =
    proj₁ $ Lemmas.length-++-≡ [ b₁ ] _ [ b₂ ] _ xs₁++ys₁≡xs₂++ys₂ refl

  @0 noconfusion : NoConfusion UTF8Char1 (Sum UTF8Char2 (Sum UTF8Char3 UTF8Char4))
  noconfusion =
    Sum.noconfusion{A = UTF8Char1} nc₁
      (Sum.noconfusion{A = UTF8Char1} nc₂ nc₃)
    where
    nc₁ : NoConfusion UTF8Char1 UTF8Char2
    nc₁{xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ a x =
      contradiction
        (toℕ (UTF8Char2.b₁ x) > 191 ∋ proj₁ (UTF8Char2.b₁range x))
        (<⇒≱ (subst (λ z → toℕ z < 192) b₁≡ (≤-trans (UTF8Char1.b₁range a) (toWitness{Q = 128 ≤? 192} _))))
      where
      open ≡-Reasoning

      @0 bs≡ :   UTF8Char1.b₁ a ∷ ys₁
               ≡ UTF8Char2.b₁ x ∷ UTF8Char2.b₂ x ∷ ys₂
      bs≡ = begin
        (UTF8Char1.b₁ a ∷ ys₁ ≡⟨ cong (_++ ys₁) (sym $ UTF8Char1.bs≡ a) ⟩
        xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
        xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) (UTF8Char2.bs≡ x) ⟩
        UTF8Char2.b₁ x ∷ UTF8Char2.b₂ x ∷ ys₂ ∎)

      @0 b₁≡ : UTF8Char1.b₁ a ≡ UTF8Char2.b₁ x
      b₁≡ = ∷-injectiveˡ (proj₁ (Lemmas.length-++-≡ [ UTF8Char1.b₁ a ] _ [ UTF8Char2.b₁ x ] _ bs≡ refl))

    nc₂ : NoConfusion UTF8Char1 UTF8Char3
    nc₂{xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ a x =
      contradiction
        (toℕ (UTF8Char3.b₁ x) > 223 ∋ proj₁ (UTF8Char3.b₁range x))
        (<⇒≱ (subst (λ z → toℕ z < 224) b₁≡ (≤-trans (UTF8Char1.b₁range a) (toWitness{Q = 128 ≤? 224} _))))
      where
      open ≡-Reasoning

      @0 bs≡ :   UTF8Char1.b₁ a ∷ ys₁
               ≡ UTF8Char3.b₁ x ∷ UTF8Char3.b₂ x ∷ UTF8Char3.b₃ x ∷ ys₂
      bs≡ = begin
        (UTF8Char1.b₁ a ∷ ys₁ ≡⟨ cong (_++ ys₁) (sym $ UTF8Char1.bs≡ a) ⟩
        xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
        xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) (UTF8Char3.bs≡ x) ⟩
        UTF8Char3.b₁ x ∷ UTF8Char3.b₂ x ∷ UTF8Char3.b₃ x ∷ ys₂ ∎)

      @0 b₁≡ : UTF8Char1.b₁ a ≡ UTF8Char3.b₁ x
      b₁≡ = ∷-injectiveˡ (proj₁ (Lemmas.length-++-≡ [ UTF8Char1.b₁ a ] _ [ UTF8Char3.b₁ x ] _ bs≡ refl))

    nc₃ : NoConfusion UTF8Char1 UTF8Char4
    nc₃{xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ a x =
      contradiction
        (toℕ (UTF8Char4.b₁ x) > 239 ∋ proj₁ (UTF8Char4.b₁range x))
        (<⇒≱ (subst (λ z → toℕ z < 240) b₁≡ (≤-trans (UTF8Char1.b₁range a) (toWitness{Q = 128 ≤? 240} _))))
      where
      open ≡-Reasoning

      @0 bs≡ :   UTF8Char1.b₁ a ∷ ys₁
               ≡ UTF8Char4.b₁ x ∷ UTF8Char4.b₂ x ∷ UTF8Char4.b₃ x ∷ UTF8Char4.b₄ x ∷ ys₂
      bs≡ = begin
        UTF8Char1.b₁ a ∷ ys₁ ≡⟨ cong (_++ ys₁) (sym $ UTF8Char1.bs≡ a) ⟩
        xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
        xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) (UTF8Char4.bs≡ x) ⟩
        UTF8Char4.b₁ x ∷ UTF8Char4.b₂ x ∷ UTF8Char4.b₃ x ∷ UTF8Char4.b₄ x ∷ ys₂ ∎

      @0 b₁≡ : UTF8Char1.b₁ a ≡ UTF8Char4.b₁ x
      b₁≡ = ∷-injectiveˡ (proj₁ (Lemmas.length-++-≡ [ UTF8Char1.b₁ a ] _ [ UTF8Char4.b₁ x ] _ bs≡ refl))

  @0 nonmalleable : NonMalleable RawUTF8Char1
  nonmalleable (mkUTF8Char1 b₁ b₁range refl) (mkUTF8Char1 ._ b₁range₁ refl) refl =
    case (‼ ≤-irrelevant b₁range b₁range₁) ret (const _) of λ where
      refl → refl

module UTF8Char2Props where
  @0 unambiguous : Unambiguous UTF8Char2
  unambiguous (mkUTF8Char2 b₁ b₂ b₁range b₂range refl) (mkUTF8Char2 .b₁ .b₂ b₁range₁ b₂range₁ refl) =
    subst₂ (λ b₁r b₂r → mkUTF8Char2 b₁ b₂ b₁range b₂range refl ≡ mkUTF8Char2 _ _ b₁r b₂r refl)
      (inRange-unique{A = ℕ}{B = UInt8} b₁range b₁range₁) (inRange-unique{A = ℕ}{B = UInt8} b₂range b₂range₁) refl

  nosubstrings : NoSubstrings UTF8Char2
  nosubstrings xs₁++ys₁≡xs₂++ys₂ (mkUTF8Char2 b₁ b₂ b₁range b₂range refl) (mkUTF8Char2 b₃ b₄ b₁range₁ b₂range₁ refl) =
    proj₁ $ Lemmas.length-++-≡ (b₁ ∷ [ b₂ ]) _ (b₃ ∷ [ b₄ ]) _ xs₁++ys₁≡xs₂++ys₂ refl

  @0 noconfusion : NoConfusion UTF8Char2 (Sum UTF8Char3 UTF8Char4)
  noconfusion =
    Sum.noconfusion{A = UTF8Char2} nc₁ nc₂
    where
    nc₁ : NoConfusion UTF8Char2 UTF8Char3
    nc₁{xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ a x =
      contradiction
        (toℕ (UTF8Char3.b₁ x) > 223 ∋ proj₁ (UTF8Char3.b₁range x))
        (<⇒≱ (subst (λ z → toℕ z < 224) b₁≡ (s≤s (proj₂ (UTF8Char2.b₁range a)))))
      where
      open ≡-Reasoning

      @0 bs≡ :   UTF8Char2.b₁ a ∷ UTF8Char2.b₂ a ∷ ys₁
              ≡ UTF8Char3.b₁ x ∷ UTF8Char3.b₂ x ∷ UTF8Char3.b₃ x ∷ ys₂
      bs≡ = begin
        (UTF8Char2.b₁ a ∷ UTF8Char2.b₂ a ∷ ys₁ ≡⟨ cong (_++ ys₁) (sym $ UTF8Char2.bs≡ a) ⟩
        xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
        xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) (UTF8Char3.bs≡ x) ⟩
        UTF8Char3.b₁ x ∷ UTF8Char3.b₂ x ∷ UTF8Char3.b₃ x ∷ ys₂ ∎)

      @0 b₁≡ : UTF8Char2.b₁ a ≡ UTF8Char3.b₁ x
      b₁≡ = ∷-injectiveˡ (proj₁ (Lemmas.length-++-≡ [ UTF8Char2.b₁ a ] _ [ UTF8Char3.b₁ x ] _ bs≡ refl))

    nc₂ : NoConfusion UTF8Char2 UTF8Char4
    nc₂{xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ a x =
      contradiction
        (toℕ (UTF8Char4.b₁ x) > 239 ∋ proj₁ (UTF8Char4.b₁range x))
        (<⇒≱ (subst (λ z → toℕ z < 240) b₁≡ (≤-trans (s≤s (proj₂ (UTF8Char2.b₁range a))) (toWitness{Q = 224 ≤? 240} _))))
      where
      open ≡-Reasoning

      @0 bs≡ :   UTF8Char2.b₁ a ∷ UTF8Char2.b₂ a ∷ ys₁
               ≡ UTF8Char4.b₁ x ∷ UTF8Char4.b₂ x ∷ UTF8Char4.b₃ x ∷ UTF8Char4.b₄ x ∷ ys₂
      bs≡ = begin
        (UTF8Char2.b₁ a ∷ UTF8Char2.b₂ a ∷ ys₁ ≡⟨ cong (_++ ys₁) (sym $ UTF8Char2.bs≡ a) ⟩
        xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
        xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) (UTF8Char4.bs≡ x) ⟩
        UTF8Char4.b₁ x ∷ UTF8Char4.b₂ x ∷ UTF8Char4.b₃ x ∷ UTF8Char4.b₄ x ∷ ys₂ ∎)
  
      @0 b₁≡ : UTF8Char2.b₁ a ≡ UTF8Char4.b₁ x
      b₁≡ = ∷-injectiveˡ (proj₁ (Lemmas.length-++-≡ [ UTF8Char2.b₁ a ] _ [ UTF8Char4.b₁ x ] _ bs≡ refl))

  @0 nonmalleable : NonMalleable RawUTF8Char2
  nonmalleable (mkUTF8Char2 b₁ b₂ b₁range b₂range refl) (mkUTF8Char2 b₃ b₄ b₁range₁ b₂range₁ refl) refl =
      case (‼ inRange-unique{A = ℕ}{B = UInt8} b₁range b₁range₁) of λ where
        refl → (case (‼ inRange-unique{A = ℕ}{B = UInt8} b₂range b₂range₁) ret (const _) of λ where
          refl → refl)

module UTF8Char3Props where
  nosubstrings : NoSubstrings UTF8Char3
  nosubstrings xs₁++ys₁≡xs₂++ys₂
    (mkUTF8Char3 b₁ b₂ b₃ b₁range  b₂range  b₃range refl)
    (mkUTF8Char3 b₄ b₅ b₆ b₁range₁ b₂range₁ b₃range₁ refl) =
    proj₁ (Lemmas.length-++-≡ (b₁ ∷ b₂ ∷ [ b₃ ]) _ (b₄ ∷ b₅ ∷ [ b₆ ]) _ xs₁++ys₁≡xs₂++ys₂ refl)

  Rep : @0 List UInt8 → Set
  Rep =
    Σₚ (ExactLengthString 3)
      λ _ els →
        Erased
          (InRange 224 239 (lookupExactLengthString els (# 0))
           × InRange 128 191 (lookupExactLengthString els (# 1))
           × InRange 128 191 (lookupExactLengthString els (# 2)))

  iso : Iso Rep UTF8Char3
  proj₁ (proj₁ iso) (mk×ₚ els@(mk×ₚ (singleton (b₁ ∷ b₂ ∷ b₃ ∷ [] ) refl) sndₚ₂) (─ (b₁range , b₂range , b₃range))) =
    mkUTF8Char3
      (lookupExactLengthString els (# 0)) (lookupExactLengthString els (# 1)) (lookupExactLengthString els (# 2)) b₁range b₂range b₃range refl
  proj₂ (proj₁ iso) (mkUTF8Char3 b₁ b₂ b₃ b₁range b₂range b₃range refl) =
    mk×ₚ (mk×ₚ self (─ refl)) (─ (b₁range , b₂range , b₃range))
  proj₁ (proj₂ iso) (mk×ₚ (mk×ₚ (singleton (b₁ ∷ b₂ ∷ b₃ ∷ []) refl) (─ refl)) (─ (b₁range , b₂range , b₃range))) =
    refl
  proj₂ (proj₂ iso) (mkUTF8Char3 b₁ b₂ b₃ b₁range b₂range b₃range refl) =
    refl

  @0 unambiguous : Unambiguous UTF8Char3
  unambiguous =
    Iso.unambiguous iso
      (Parallel.unambiguous
        Parallel.ExactLengthString.unambiguous
        (λ {xs} a →
          erased-unique
            (×-unique (inRange-unique{A = ℕ}{B = UInt8})
              (×-unique (inRange-unique{A = ℕ}{B = UInt8})
                (inRange-unique{A = ℕ}{B = UInt8})))))

  noconfusion : NoConfusion UTF8Char3 UTF8Char4
  noconfusion{xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ a x =
    contradiction
      (toℕ (UTF8Char4.b₁ x) > 239 ∋ proj₁ (UTF8Char4.b₁range x))
      (<⇒≱ (subst₀ (λ z → toℕ z < 240) b₁≡ (s≤s $ proj₂ (UTF8Char3.b₁range a))))
    where
    open ≡-Reasoning

    @0 bs≡ :   UTF8Char3.b₁ a ∷ UTF8Char3.b₂ a ∷ UTF8Char3.b₃ a ∷ ys₁
             ≡ UTF8Char4.b₁ x ∷ UTF8Char4.b₂ x ∷ UTF8Char4.b₃ x ∷ UTF8Char4.b₄ x ∷ ys₂
    bs≡ = begin
      (UTF8Char3.b₁ a ∷ UTF8Char3.b₂ a ∷ UTF8Char3.b₃ a ∷ ys₁ ≡⟨ cong (_++ ys₁) (sym $ UTF8Char3.bs≡ a) ⟩
      xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
      xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) (UTF8Char4.bs≡ x) ⟩
      UTF8Char4.b₁ x ∷ UTF8Char4.b₂ x ∷ UTF8Char4.b₃ x ∷ UTF8Char4.b₄ x ∷ ys₂ ∎)

    @0 b₁≡ : UTF8Char3.b₁ a ≡ UTF8Char4.b₁ x
    b₁≡ = ∷-injectiveˡ (proj₁ (Lemmas.length-++-≡ [ UTF8Char3.b₁ a ] _ [ UTF8Char4.b₁ x ] _ bs≡ refl))

  @0 nonmalleable : NonMalleable RawUTF8Char3
  nonmalleable (mkUTF8Char3 b₁ b₂ b₃ b₁range b₂range b₃range refl) (mkUTF8Char3 b₄ b₅ b₆ b₁range₁ b₂range₁ b₃range₁ refl) refl =
    case (‼ inRange-unique{A = ℕ}{B = UInt8} b₁range b₁range₁) of λ where
      refl → (case (‼ inRange-unique{A = ℕ}{B = UInt8} b₂range b₂range₁) ret (const _) of λ where
        refl → (case (‼ inRange-unique{A = ℕ}{B = UInt8} b₃range b₃range₁) ret (const _) of λ where
          refl → refl))

module UTF8Char4Props where
  nosubstrings : NoSubstrings UTF8Char4
  nosubstrings xs₁++ys₁≡xs₂++ys₂ (mkUTF8Char4 b₁ b₂ b₃ b₄ b₁range b₂range b₃range b₄ranger refl) (mkUTF8Char4 b₅ b₆ b₇ b₈ b₁range₁ b₂range₁ b₃range₁ b₄range₁ refl) =
    proj₁ (Lemmas.length-++-≡ (b₁ ∷ b₂ ∷ b₃ ∷ [ b₄ ]) _ (b₅ ∷ b₆ ∷ b₇ ∷ [ b₈ ]) _ xs₁++ys₁≡xs₂++ys₂ refl)

  Rep : @0 List UInt8 → Set
  Rep =
    Σₚ (ExactLengthString 4)
      λ _ els →
        Erased
          (  InRange 240 247 (lookupExactLengthString els (# 0))
           × InRange 128 191 (lookupExactLengthString els (# 1))
           × InRange 128 191 (lookupExactLengthString els (# 2))
           × InRange 128 191 (lookupExactLengthString els (# 3)))

  equiv : Equivalent Rep UTF8Char4
  proj₁ equiv (mk×ₚ (mk×ₚ (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) refl) (─ refl)) (─ (fst , fst₁ , fst₂ , snd))) =
    mkUTF8Char4 x x₁ x₂ x₃ fst fst₁ fst₂ snd refl
  proj₂ equiv (mkUTF8Char4 b₁ b₂ b₃ b₄ b₁range b₂range b₃range b₄range refl) =
    mk×ₚ (mk×ₚ self (─ refl)) (─ (b₁range , b₂range , b₃range , b₄range))

  iso : Iso Rep UTF8Char4
  proj₁ iso = equiv
  proj₁ (proj₂ iso) (mk×ₚ (mk×ₚ (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) refl) (─ refl)) (─ (r₁ , r₂ , r₃ , r₄))) = refl
  proj₂ (proj₂ iso) (mkUTF8Char4 b₁ b₂ b₃ b₄ b₁range b₂range b₃range b₄range refl) = refl

  @0 unambiguous : Unambiguous UTF8Char4
  unambiguous =
    Iso.unambiguous iso
      (Parallel.unambiguous Parallel.ExactLengthString.unambiguous
        (λ {xs} a →
          erased-unique
            (×-unique (inRange-unique{A = ℕ}{B = UInt8})
              (×-unique (inRange-unique{A = ℕ}{B = UInt8})
                (×-unique (inRange-unique{A = ℕ}{B = UInt8})
                  (inRange-unique{A = ℕ}{B = UInt8}))))))

  @0 nonmalleable : NonMalleable RawUTF8Char4
  nonmalleable (mkUTF8Char4 b₁ b₂ b₃ b₄ b₁range b₂range b₃range b₄range refl) (mkUTF8Char4 b₅ b₆ b₇ b₈ b₁range₁ b₂range₁ b₃range₁ b₄range₁ refl) refl =
    case (‼ inRange-unique{A = ℕ}{B = UInt8} b₁range b₁range₁) of λ where
      refl → (case (‼ inRange-unique{A = ℕ}{B = UInt8} b₂range b₂range₁) ret (const _) of λ where
        refl → (case (‼ inRange-unique{A = ℕ}{B = UInt8} b₃range b₃range₁) ret (const _) of λ where
          refl → (case (‼ inRange-unique{A = ℕ}{B = UInt8} b₄range b₄range₁) ret (const _) of λ where
            refl → refl)))

module UTF8CharProps where
  iso : Iso UTF8CharRep UTF8Char
  proj₁ iso = equivalentChar
  proj₁ (proj₂ iso) (inj₁ x) = refl
  proj₁ (proj₂ iso) (inj₂ (inj₁ x)) = refl
  proj₁ (proj₂ iso) (inj₂ (inj₂ (inj₁ x))) = refl
  proj₁ (proj₂ iso) (inj₂ (inj₂ (inj₂ x))) = refl
  proj₂ (proj₂ iso) (utf81 x) = refl
  proj₂ (proj₂ iso) (utf82 x) = refl
  proj₂ (proj₂ iso) (utf83 x) = refl
  proj₂ (proj₂ iso) (utf84 x) = refl

  @0 unambiguous : Unambiguous UTF8Char
  unambiguous =
    Iso.unambiguous iso
      (Sum.unambiguous
        UTF8Char1Props.unambiguous
        (Sum.unambiguous
          UTF8Char2Props.unambiguous
          (Sum.unambiguous
            UTF8Char3Props.unambiguous
            UTF8Char4Props.unambiguous
            UTF8Char3Props.noconfusion)
          UTF8Char2Props.noconfusion)
        UTF8Char1Props.noconfusion)

  @0 nonempty : NonEmpty UTF8Char
  nonempty (utf81 ()) refl
  nonempty (utf82 ()) refl
  nonempty (utf83 ()) refl
  nonempty (utf84 ()) refl

  @0 nosubstrings : NoSubstrings UTF8Char
  nosubstrings =
    Iso.nosubstrings equivalentChar
      (Sum.nosubstrings
        UTF8Char1Props.nosubstrings
        (Sum.nosubstrings UTF8Char2Props.nosubstrings
          (Sum.nosubstrings
            UTF8Char3Props.nosubstrings
            UTF8Char4Props.nosubstrings
            UTF8Char3Props.noconfusion)
          UTF8Char2Props.noconfusion)
        UTF8Char1Props.noconfusion)

  @0 nonmalleable : NonMalleable RawUTF8Char
  nonmalleable =
    Iso.nonmalleable iso RawUTF8CharRep
      (Sum.nonmalleable UTF8Char1Props.nonmalleable
      (Sum.nonmalleable UTF8Char2Props.nonmalleable
      (Sum.nonmalleable UTF8Char3Props.nonmalleable
                        UTF8Char4Props.nonmalleable)))

@0 unambiguous : Unambiguous UTF8
unambiguous =
  IList.unambiguous
    UTF8CharProps.unambiguous UTF8CharProps.nonempty UTF8CharProps.nosubstrings

@0 nonmalleable : NonMalleable RawUTF8
nonmalleable snd snd₁ x =
  IList.nonmalleable UTF8CharProps.nonempty UTF8CharProps.nosubstrings UTF8CharProps.nonmalleable snd snd₁ x

sizeUnique : ∀ {@0 bs} → (a₁ a₂ : UTF8 bs) → UTF8.size a₁ ≡ UTF8.size a₂
sizeUnique a₁ a₂ = ‼ cong UTF8.size (unambiguous a₁ a₂)

instance
  UTF8Char1Eq≋ : Eq≋ UTF8Char1
  Eq≋._≋?_ UTF8Char1Eq≋ (mkUTF8Char1 b₁₁ b₁range₁ refl) (mkUTF8Char1 b₁₂ b₁range₂ refl) =
    case b₁₁ ≟ b₁₂ ret (const _) of λ where
      (yes refl) →
        let b₁range≡ : Erased (b₁range₁ ≡ b₁range₂)
            b₁range≡ = ─ ≤-unique b₁range₁ b₁range₂
        in
        yes (mk≋ refl
               (subst (λ x → mkUTF8Char1 b₁₁ b₁range₁ refl ≡ mkUTF8Char1 b₁₁ x refl)
                 (‼ (¡ b₁range≡))
                 refl))
      (no b≢)    →
        no λ where ≋-refl → contradiction refl b≢

  UTF8Char2Eq≋ : Eq≋ UTF8Char2
  Eq≋._≋?_ UTF8Char2Eq≋ (mkUTF8Char2 b₁ b₂ b₁range b₂range refl) (mkUTF8Char2 b₃ b₄ b₁range₁ b₂range₁ refl) =
    case (b₁ ∷ [ b₂ ] ≟ b₃ ∷ [ b₄ ]) ret (const _) of λ where
      (yes refl) →
        let b₁range≡ : Erased (b₁range ≡ b₁range₁)
            b₁range≡ = ─ inRange-unique{l = 192}{x = b₁} b₁range b₁range₁

            b₂range≡ : Erased (b₂range ≡ b₂range₁)
            b₂range≡ = ─ inRange-unique{l = 128}{x = b₂} b₂range b₂range₁
        in
        yes (mk≋ refl
          (subst₂ (λ x y → mkUTF8Char2 b₁ b₂ b₁range b₂range refl ≡ mkUTF8Char2 b₁ b₂ x y refl)
            (‼ (¡ b₁range≡)) (‼ (¡ b₂range≡)) refl))
      (no  b≢)   → no λ where ≋-refl → contradiction refl b≢

  UTF8Char3Eq≋ : Eq≋ UTF8Char3
  Eq≋._≋?_ UTF8Char3Eq≋ (mkUTF8Char3 b₁ b₂ b₃ b₁range b₂range b₃range refl) (mkUTF8Char3 b₁' b₂' b₃' b₁range' b₂range' b₃range' refl) =
    case (b₁ ∷ b₂ ∷ [ b₃ ] ≟ b₁' ∷ b₂' ∷ [ b₃' ]) ret (const _) of λ where
      (no b≢) → no λ where ≋-refl → contradiction refl b≢
      (yes refl) →
        yes (mk≋ refl
          (subst₂
             (λ x y →
                mkUTF8Char3 b₁ b₂ b₃ b₁range b₂range b₃range refl ≡
                mkUTF8Char3 b₁ b₂ b₃ x y b₃range' refl)
             (inRange-unique{l = 224}{x = b₁} b₁range b₁range')
             (inRange-unique{l = 128}{x = b₂} b₂range b₂range')
             (subst
                (λ x →
                   mkUTF8Char3 b₁ b₂ b₃ b₁range b₂range b₃range refl ≡
                   mkUTF8Char3 b₁ b₂ b₃ b₁range b₂range x refl)
                (inRange-unique{l = 128}{x = b₃} b₃range b₃range') refl)))

  UTF8Char4Eq≋ : Eq≋ UTF8Char4
  Eq≋._≋?_ UTF8Char4Eq≋ (mkUTF8Char4 b₁ b₂ b₃ b₄ b₁range b₂range b₃range b₄range refl) (mkUTF8Char4 b₁' b₂' b₃' b₄' b₁range' b₂range' b₃range' b₄range' refl) =
    case (b₁ ∷ b₂ ∷ b₃ ∷ [ b₄ ] ≟ b₁' ∷ b₂' ∷ b₃' ∷ [ b₄' ]) ret (const _) of λ where
      (no b≢) → no λ where ≋-refl → contradiction refl b≢
      (yes refl) →
        yes (mk≋ refl
          (subst₂
            (λ x y →
                mkUTF8Char4 b₁ b₂ b₃ b₄ b₁range b₂range b₃range  b₄range refl ≡
                mkUTF8Char4 b₁ b₂ b₃ b₄ x       y       b₃range' b₄range' refl)
            (inRange-unique{l = 240}{x = b₁} b₁range b₁range')
            (inRange-unique{l = 128}{x = b₂} b₂range b₂range')
            (subst₂
              (λ x y → mkUTF8Char4 b₁ b₂ b₃ b₄ b₁range b₂range b₃range  b₄range refl ≡
                       mkUTF8Char4 b₁ b₂ b₃ b₄ b₁range b₂range x        y       refl)
              (inRange-unique{l = 128}{x = b₃} b₃range b₃range')
              (inRange-unique{l = 128}{x = b₄} b₄range b₄range')
              refl)))

  UTF8CharEq≋ : Eq≋ UTF8Char
  (UTF8CharEq≋ Eq≋.≋? utf81 x) (utf81 x₁)
    with x ≋? x₁
  ... | yes ≋-refl = yes ≋-refl
  ... | no ≢ = no λ where ≋-refl → contradiction ≋-refl ≢
  (UTF8CharEq≋ Eq≋.≋? utf81 x) (utf82 x₁) = no λ { (mk≋ refl ())}
  (UTF8CharEq≋ Eq≋.≋? utf81 x) (utf83 x₁) = no λ { (mk≋ refl ())}
  (UTF8CharEq≋ Eq≋.≋? utf81 x) (utf84 x₁) = no λ { (mk≋ refl ())}
  (UTF8CharEq≋ Eq≋.≋? utf82 x) (utf81 x₁) = no λ { (mk≋ refl ())}
  (UTF8CharEq≋ Eq≋.≋? utf82 x) (utf82 x₁)
    with x ≋? x₁
  ... | yes ≋-refl = yes ≋-refl
  ... | no  ≢      = no λ where ≋-refl → contradiction ≋-refl ≢
  (UTF8CharEq≋ Eq≋.≋? utf82 x) (utf83 x₁) = no λ { (mk≋ refl ())}
  (UTF8CharEq≋ Eq≋.≋? utf82 x) (utf84 x₁) = no λ { (mk≋ refl ())}
  (UTF8CharEq≋ Eq≋.≋? utf83 x) (utf81 x₁) = no λ { (mk≋ refl ())}
  (UTF8CharEq≋ Eq≋.≋? utf83 x) (utf82 x₁) = no λ { (mk≋ refl ())}
  (UTF8CharEq≋ Eq≋.≋? utf83 x) (utf83 x₁)
    with x ≋? x₁
  ... | yes ≋-refl = yes ≋-refl
  ... | no ≢       = no λ where ≋-refl → contradiction ≋-refl ≢
  (UTF8CharEq≋ Eq≋.≋? utf83 x) (utf84 x₁) = no λ { (mk≋ refl ())}
  (UTF8CharEq≋ Eq≋.≋? utf84 x) (utf81 x₁) = no λ { (mk≋ refl ())}
  (UTF8CharEq≋ Eq≋.≋? utf84 x) (utf82 x₁) = no λ { (mk≋ refl ())}
  (UTF8CharEq≋ Eq≋.≋? utf84 x) (utf83 x₁) = no λ { (mk≋ refl ())}
  (UTF8CharEq≋ Eq≋.≋? utf84 x) (utf84 x₁)
    with x ≋? x₁
  ... | yes ≋-refl = yes ≋-refl
  ... | no ≢       = no λ where ≋-refl → contradiction ≋-refl ≢

  UTF8CharEq : Eq (Exists─ (List UInt8) UTF8Char)
  UTF8CharEq = Eq≋⇒Eq it

  UTF8Eq : Eq (Exists─ _ UTF8)
  UTF8Eq = IList.IListEq

  UTF8Eq≋ : Eq≋ UTF8
  UTF8Eq≋ = IList.IListEq≋
