open import Armor.Binary renaming (module Base64 to B64)
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Parallel
import      Armor.Grammar.Option
import      Armor.Grammar.Seq
import      Armor.Grammar.Sum
open import Armor.Prelude
import      Armor.Data.Base64.TCB as Base64
import      Data.Nat.DivMod       as Nat
import      Data.Nat.Properties   as Nat

open Armor.Grammar.Definitions          Char
open Armor.Grammar.IList                Char
open Armor.Grammar.Parallel             Char
open Armor.Grammar.Option               Char
open Armor.Grammar.Seq                  Char
open Armor.Grammar.Sum                  Char
open ≡-Reasoning

module Armor.Data.Base64.Properties where

module Base64Char where
  Rep : @0 List Char → Set
  Rep =
    Σₚ (λ x → Erased (ExactLengthString 1 x))
       λ where
         ._ (─ xs) →
           let @0 c : Char
               c = lookupExactLengthString xs (# 0)
           in Exists─ (c ∈ B64.charset) (λ c∈ → Singleton (Any.index c∈))

  equiv : Equivalent Rep Base64.Base64Char
  proj₁ equiv {xs“} (mk×ₚ (─ xs'@(mk×ₚ self (─ xsLen))) (─ c∈ , i)) =
    Base64.mk64 (lookupExactLengthString xs' (# 0)) c∈ i (‼ lem xsLen)
    where
    @0 lem : ∀ {xs“} (xsLen : length xs“ ≡ 1)
             → xs“ ≡ [ lookupExactLengthString (mk×ₚ (singleton xs“ refl) (─ xsLen)) (# 0) ]
    lem {x ∷ []} refl = refl
  proj₂ equiv (Base64.mk64 c c∈ i refl) =
    mk×ₚ (─ (mk×ₚ (singleton (c ∷ []) refl) (─ refl))) ((─ c∈) , i)

  all2IList : ∀ {bs} → All (_∈ B64.charset) bs → IList Base64.Base64Char bs
  all2IList All.[] = nil
  all2IList{c ∷ cs} (c∈ All.∷ a) =
    cons (mkIListCons (Base64.mk64 c c∈ self refl) (all2IList a) refl)

  @0 iList2All : ∀ {@0 bs} → IList Base64.Base64Char bs → All (λ x → Base64.Base64Char [ x ]) bs
  iList2All nil = All.[]
  iList2All{bs = .(c ∷ bs₂)} (consIList{bs₂ = bs₂} (Base64.mk64 c c∈ i refl) tail₁ refl) =
    All._∷_ (Base64.mk64 c c∈ i refl) (iList2All{bs₂} tail₁)

  @0 nosubstrings : NoSubstrings Base64.Base64Char
  nosubstrings{xs₁ = xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ (Base64.mk64 c c∈ i bs≡) (Base64.mk64 c₁ c∈₁ i₁ bs≡₁) =
    begin xs₁ ≡⟨ bs≡ ⟩
          [ c ] ≡⟨ cong [_] c≡ ⟩
          [ c₁ ] ≡⟨ sym bs≡₁ ⟩
          xs₂ ∎
    where
    @0 c≡ : c ≡ c₁
    c≡ =
      ∷-injectiveˡ (begin [ c ] ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
                          xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
                          xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
                          [ c₁ ] ++ ys₂ ∎)

  @0 nonempty : NonEmpty Base64.Base64Char
  nonempty () refl

  @0 unambiguous : Unambiguous Base64.Base64Char
  unambiguous = ua
    where
    ua : ∀ {@0 xs} → (a₁ a₂ : Base64.Base64Char xs) → a₁ ≡ a₂
    ua (Base64.mk64 c c∈ i@(singleton x x≡) refl) (Base64.mk64 .c c∈₁ i₁@(singleton x₁ x₁≡) refl) =
      subst₀ (λ c∈' → ∀ i' → Base64.mk64 c c∈ i refl ≡ Base64.mk64 c c∈' i' refl)
        c∈≡
        (λ where
          (singleton x' x'≡) → ‼
            let @0 x≡x' : x ≡ x'
                x≡x' = trans₀ x≡ (sym x'≡)
            in
            subst₀
              (λ y →
                 ∀ (y≡ : y ≡ Any.index c∈) →
                 Base64.mk64 _ _ (singleton x x≡) _ ≡
                 Base64.mk64 _ _ (singleton y y≡) _)
              x≡x'
              (λ y≡ →
                subst₀ (λ y≡ → _ ≡ Base64.mk64 c c∈ (singleton x y≡) refl)
                  (≡-unique x≡ _) refl)
              x'≡)
        i₁
      where
      @0 c∈≡ : c∈ ≡ c∈₁
      c∈≡ = ∈-unique (toWitness{Q = unique? _} tt) c∈ c∈₁

module Base64Pad where
  Rep₁ : @0 List Char → Set
  Rep₁ =  &ₚ (&ₚ Base64.Base64Char Base64.Base64Char)
         (&ₚ (Σₚ Base64.Base64Char (λ xs c → toℕ (↑ Base64.Base64Char.i c) % 2 ^ 2 ≡ 0))
             (λ x → Erased (x ≡ [ '=' ])))
  
  equiv₁ : Equivalent Rep₁ Base64.Base64Pad1
  proj₁ equiv₁ (mk&ₚ (mk&ₚ (Base64.mk64 c c∈ i refl) (Base64.mk64 c₁ c∈₁ i₁ refl) refl) (mk&ₚ (mk×ₚ (Base64.mk64 c₂ c∈₂ i₂ refl) sndₚ₃) (─ refl) refl) refl) = Base64.mk64P1 (Base64.mk64 c c∈ i refl) (Base64.mk64 c₁ c∈₁ i₁ refl) (Base64.mk64 c₂ c∈₂ i₂ refl) sndₚ₃ refl
  proj₂ equiv₁ (Base64.mk64P1 c₁ c₂ c₃ pad refl) = mk&ₚ (mk&ₚ c₁ c₂ refl) (mk&ₚ (mk×ₚ c₃ (‼ pad)) (─ refl) refl) refl

  Rep₂ : @0 List Char → Set
  Rep₂ =  &ₚ Base64.Base64Char
         (&ₚ (Σₚ Base64.Base64Char (λ xs c → toℕ (↑ Base64.Base64Char.i c) % 2 ^ 4 ≡ 0))
             (λ x → Erased (x ≡ '=' ∷ [ '=' ])))

  equiv₂ : Equivalent Rep₂ Base64.Base64Pad2
  proj₁ equiv₂ (mk&ₚ (Base64.mk64 c c∈ i refl) (mk&ₚ (mk×ₚ (Base64.mk64 c₁ c∈₁ i₁ refl) sndₚ₂) (─ refl) refl) refl) = Base64.mk64P2 (Base64.mk64 c c∈ i refl) (Base64.mk64 c₁ c∈₁ i₁ refl) sndₚ₂ refl
  proj₂ equiv₂ (Base64.mk64P2 c₁ c₂ pad refl) = mk&ₚ c₁ (mk&ₚ (mk×ₚ c₂ (‼ pad)) (─ refl) refl) refl

  Rep : @0 List Char → Set
  Rep = Option (Sum Base64.Base64Pad1 Base64.Base64Pad2)

  equiv : Equivalent Rep Base64.Base64Pad
  proj₁ equiv none = Base64.pad0 refl
  proj₁ equiv (some (Sum.inj₁ (Base64.mk64P1 c₁ c₂ c₃ pad refl))) = Base64.pad1 (Base64.mk64P1 c₁ c₂ c₃ pad refl)
  proj₁ equiv (some (Sum.inj₂ (Base64.mk64P2 c₁ c₂ pad refl))) = Base64.pad2 (Base64.mk64P2 c₁ c₂ pad refl)
  proj₂ equiv (Base64.pad0 refl) = none
  proj₂ equiv (Base64.pad1 (Base64.mk64P1 c₁ c₂ c₃ pad refl)) = some (Sum.inj₁ (Base64.mk64P1 c₁ c₂ c₃ pad refl))
  proj₂ equiv (Base64.pad2 (Base64.mk64P2 c₁ c₂ pad refl)) = some (Sum.inj₂ (Base64.mk64P2 c₁ c₂ pad refl))

  @0 p%4≡0 : ∀ {@0 p} → Base64.Base64Pad p → length p % 4 ≡ 0
  p%4≡0 (Base64.pad0 refl) = refl
  p%4≡0 (Base64.pad1 (Base64.mk64P1 c₁ c₂ c₃ pad refl)) = refl
  p%4≡0 (Base64.pad2 (Base64.mk64P2 c₁ c₂ pad refl)) = refl

  forcebs : ∀ {@0 xs₁ bs₁ ys₁ xs₂ ys₂ c₁ c₂ c₃ c₄}
            → Sum Base64.Base64Pad1 Base64.Base64Pad2 xs₂
            → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂
            → xs₁ ≡ c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs₁
            → xs₂ ≡ c₁ ∷ c₂ ∷ c₃ ∷ [ c₄ ]
  forcebs{bs₁ = bs₁}{ys₁} (Sum.inj₁ (Base64.mk64P1 c₁ c₂ c₃ pad refl)) ++≡ refl = ‼ proj₁ (Lemmas.length-++-≡ _ _ _ (bs₁ ++ ys₁) (sym ++≡) refl)
  forcebs (Sum.inj₂ (Base64.mk64P2 c₁ c₂ pad refl)) ++≡ refl = ‼ proj₁ (Lemmas.length-++-≡ _ _ _ _ (sym ++≡) refl)

  nonempty : NonEmpty (Sum Base64.Base64Pad1 Base64.Base64Pad2)
  nonempty (Sum.inj₁ ()) refl
  nonempty (Sum.inj₂ ()) refl

  @0 char₁ : ∀ {@0 b bs} → Base64.Base64Pad (b ∷ bs) → b ∈ B64.charset
  char₁ (Base64.pad1 (Base64.mk64P1 (Base64.mk64 c c∈ i refl) c₂ c₃ pad refl)) = c∈
  char₁ (Base64.pad2 (Base64.mk64P2 (Base64.mk64 c c∈ i refl) c₂ pad refl)) = c∈

  c₄∉ : ∀ {@0 c₁ c₂ c₃ c₄} → Sum Base64.Base64Pad1 Base64.Base64Pad2 (c₁ ∷ c₂ ∷ c₃ ∷ [ c₄ ]) → c₄ ∉ B64.charset
  c₄∉ (Sum.inj₁ (Base64.mk64P1 c₁ c₂ c₃ pad refl)) = toWitnessFalse {Q = _ ∈? _} tt
  c₄∉ (Sum.inj₂ (Base64.mk64P2 c₁ c₂ pad refl)) = toWitnessFalse{Q = _ ∈? _} tt

  @0 unambiguous : Unambiguous Base64.Base64Pad
  unambiguous (Base64.pad0 refl) (Base64.pad0 refl) = refl
  unambiguous (Base64.pad0 refl) (Base64.pad1 ())
  unambiguous (Base64.pad0 refl) (Base64.pad2 ())
  unambiguous (Base64.pad1 (Base64.mk64P1 c₁ c₂ c₃ pad ())) (Base64.pad0 refl)
  unambiguous (Base64.pad1 (Base64.mk64P1 c₁ c₂ c₃ pad refl)) (Base64.pad1 (Base64.mk64P1 c₄ c₅ c₆ pad₁ refl)) =
    case (Base64Char.unambiguous c₁ c₄ ,′ Base64Char.unambiguous c₂ c₅ ,′ Base64Char.unambiguous c₃ c₆) of λ where
      (refl , refl , refl) → ‼ (case ≡-unique pad pad₁ of λ where
        refl → refl)
  unambiguous (Base64.pad1 (Base64.mk64P1 (Base64.mk64! {c∈ = c₁₁∈} i₁₁) (Base64.mk64! {c∈ = c₁₂∈} i₁₂) (Base64.mk64! {c∈ = c₁₃∈} i₁₃) pad refl)) (Base64.pad2 (Base64.mk64P2 (Base64.mk64! {c∈ = c₂₁∈} i₂₁) (Base64.mk64! {c∈ = c₂₂∈} i₂) pad₁ refl)) =
    contradiction c₁₃∈ (toWitnessFalse{Q = _ ∈? _} tt)
  unambiguous (Base64.pad2 (Base64.mk64P2 c₁ c₂ pad ())) (Base64.pad0 refl)
  unambiguous (Base64.mk64P2!{Base64.mk64! _}{Base64.mk64! _}) (Base64.mk64P1!{Base64.mk64! _}{Base64.mk64! _}{Base64.mk64! {c∈ = c₂₃∈} _}) =
    contradiction c₂₃∈ (toWitnessFalse{Q = _ ∈? _} tt)
  unambiguous (Base64.pad2 (Base64.mk64P2 c₁ c₂ pad refl)) (Base64.pad2 (Base64.mk64P2 c₃ c₄ pad₁ refl)) =
    case (Base64Char.unambiguous c₁ c₃) ,′ (Base64Char.unambiguous c₂ c₄) of λ where
      (refl , refl) → ‼ (case ≡-unique pad pad₁ of λ where
        refl → refl)

module Base64Str where
  Rep : @0 List Char → Set
  Rep = &ₚ (IList (&ₚ Base64.Base64Char (&ₚ Base64.Base64Char (&ₚ Base64.Base64Char Base64.Base64Char)))) Base64Pad.Rep

  Repₛ : @0 List Char → Set
  Repₛ = IList (&ₚ Base64.Base64Char (&ₚ Base64.Base64Char (&ₚ Base64.Base64Char Base64.Base64Char)))

  equivₛ : Equivalent Repₛ ((IList Base64.Base64Char) ×ₚ (λ x → Erased (length x % 4 ≡ 0)))
  proj₁ equivₛ x = equivₛ₁WF x (<-wellFounded _)
    where
    open import Data.Nat.Induction
      hiding (Acc)

    equivₛ₁WF : ∀ {@0 bs} → (cs : Repₛ bs) → @0 Acc _<_ (lengthIList cs) → ((IList Base64.Base64Char) ×ₚ (λ x → Erased (length x % 4 ≡ 0))) bs
    equivₛ₁WF nil (acc rs) = mk×ₚ nil (─ refl)
    equivₛ₁WF (consIList{bs₂ = bsₜ} (mk&ₚ fstₚ₁@(Base64.mk64 _ _ _ refl) (mk&ₚ fstₚ₂@(Base64.mk64 _ _ _ refl) (mk&ₚ fstₚ₃@(Base64.mk64 _ _ _ refl) sndₚ₂@(Base64.mk64 _ _ _ refl) refl) refl) refl) tail₁ refl) (acc rs) =
      case tail' of λ where
        (mk×ₚ fstₚ₁' sndₚ₁') →
          mk×ₚ{B = λ x _ → Erased (length x % 4 ≡ 0)} (consIList fstₚ₁ (consIList fstₚ₂ (consIList fstₚ₃ (consIList sndₚ₂ fstₚ₁' refl) refl) refl) refl) sndₚ₁'
      where
      tail' : ((IList Base64.Base64Char) ×ₚ (λ x → Erased (length x % 4 ≡ 0))) bsₜ
      tail' = equivₛ₁WF tail₁ (rs _ Nat.≤-refl)
  proj₂ equivₛ x = equivₛ₂WF x (<-wellFounded _)
    where
    open import Data.Nat.Induction
      hiding (Acc)

    equivₛ₂WF : ∀ {@0 bs} → (cs : ((IList Base64.Base64Char) ×ₚ (λ x → Erased (length x % 4 ≡ 0))) bs) → @0 Acc _<_ (lengthIList (fstₚ cs)) → Repₛ bs
    equivₛ₂WF (mk×ₚ nil _) (WellFounded.acc rs) = nil
    equivₛ₂WF (mk×ₚ (consIList fstₚ₁@(Base64.mk64 _ _ _ refl) (consIList fstₚ₂@(Base64.mk64 _ _ _ refl) (consIList fstₚ₃@(Base64.mk64 _ _ _ refl) (consIList{bs₂ = bs₂} fstₚ₄@(Base64.mk64 _ _ _ refl) tail₁ refl) refl) refl) refl) sndₚ₁) (WellFounded.acc rs) =
      consIList (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ (mk&ₚ fstₚ₃ fstₚ₄ refl) refl) refl) tail' refl
      where
      tail' : Repₛ bs₂
      tail' = equivₛ₂WF (mk×ₚ tail₁ sndₚ₁) (rs _ (Nat.m≤n+m (suc (lengthIList tail₁)) 3))

  equiv : Equivalent Rep Base64.Base64Str
  proj₁ equiv{xs} (mk&ₚ{bs₁}{bs₂} fstₚ₁ sndₚ₁ bs≡) =
    Base64.mk64Str (fstₚ l) (¡ sndₚ l) (proj₁ Base64Pad.equiv sndₚ₁) bs≡
    where
    l = proj₁ equivₛ fstₚ₁
  proj₂ equiv (Base64.mk64Str str strLen pad bs≡) =
    mk&ₚ l (proj₂ Base64Pad.equiv pad) bs≡
    where
    l = proj₂ equivₛ (mk×ₚ str (─ strLen))

  char∈ : ∀ {b bs} → b ∈ bs → Base64.Base64Str bs → b ∈ B64.charset ⊎ b ≡ '='
  char∈ b∈bs str = help (proj₂ equiv str) b∈bs
    where
    helpₚ : ∀ {b bs} → b ∈ bs → Sum Base64.Base64Pad1 Base64.Base64Pad2 bs → b ∈ B64.charset ⊎ b ≡ '='
    helpₚ{b} (here refl) (inj₁ (Base64.mk64P1 (Base64.mk64 c c∈ i refl) c₂ c₃ pad bs≡)) =
      inj₁ (uneraseDec (subst₀ (_∈ B64.charset) (sym (∷-injectiveˡ bs≡)) c∈) (_ ∈? _))
    helpₚ (here refl) (inj₂ (Base64.mk64P2 (Base64.mk64 c c∈ i refl) c₂ pad bs≡)) =
      inj₁ (uneraseDec (subst₀ (_∈ B64.charset) (sym (∷-injectiveˡ bs≡)) c∈) (_ ∈? _))
    helpₚ (there (here refl)) (inj₁ (Base64.mk64P1 c₁@(Base64.mk64 _ _ _ refl) c₂@(Base64.mk64 c c∈ i refl) c₃ pad bs≡)) =
      inj₁ (uneraseDec (subst₀ (_∈ B64.charset) (sym (∷-injectiveˡ (∷-injectiveʳ bs≡))) c∈) (_ ∈? _))
    helpₚ (there (here refl)) (inj₂ (Base64.mk64P2 c₁@(Base64.mk64 _ _ _ refl) c₂@(Base64.mk64 c c∈ i refl) pad bs≡)) =
      inj₁ (uneraseDec (subst₀ (_∈ B64.charset) (sym (∷-injectiveˡ (∷-injectiveʳ bs≡))) c∈) (_ ∈? _))
    helpₚ (there (there (here refl))) (inj₁ (Base64.mk64P1 c₁@(Base64.mk64 _ _ _ refl) c₂@(Base64.mk64 _ _ _ refl) c₃@(Base64.mk64 c c∈ i refl) pad bs≡)) =
      inj₁ (uneraseDec (subst₀ (_∈ B64.charset) (sym (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ bs≡)))) c∈) (_ ∈? _))
    helpₚ (there (there (here refl))) (inj₂ (Base64.mk64P2 c₁@(Base64.mk64 _ _ _ refl) c₂@(Base64.mk64 _ _ _ refl) pad bs≡)) =
      inj₂ (‼ ∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ bs≡)))
    helpₚ (there (there (there (here refl)))) (inj₁ (Base64.mk64P1 c₁@(Base64.mk64 _ _ _ refl) c₂@(Base64.mk64 _ _ _ refl) c₃@(Base64.mk64 _ _ _ refl) pad bs≡)) =
      inj₂ (‼ ∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ (∷-injectiveʳ bs≡))))
    helpₚ (there (there (there (here refl)))) (inj₂ (Base64.mk64P2 c₁@(Base64.mk64 _ _ _ refl) c₂@(Base64.mk64 _ _ _ refl) pad bs≡)) =
      inj₂ (‼ ∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ (∷-injectiveʳ bs≡))))
    helpₚ{b}{bs} (there (there (there (there{xs = xs} b∈)))) (inj₁ (Base64.mk64P1 c₁@(Base64.mk64 _ _ _ refl) c₂@(Base64.mk64 _ _ _ refl) c₃@(Base64.mk64 _ _ _ refl) pad bs≡)) =
      contradiction b∈
        (subst₀ (¬_ ∘ (b ∈_))
          ([] ≡ xs ∋
            proj₂ (Lemmas.length-++-≡ _ _ _ _ (trans (++-identityʳ _) (sym bs≡)) refl))
          λ ())
    helpₚ{b} (there (there (there (there{xs = xs} b∈)))) (inj₂ (Base64.mk64P2 c₁@(Base64.mk64 _ _ _ refl) c₂@(Base64.mk64 _ _ _ refl) pad bs≡)) =
      contradiction b∈
        ((subst₀ (¬_ ∘ (b ∈_))
          ([] ≡ xs ∋
            proj₂ (Lemmas.length-++-≡ _ _ _ _ (trans (++-identityʳ _) (sym bs≡)) refl))
          λ ()))

    help : ∀ {b bs} → Rep bs → b ∈ bs → b ∈ B64.charset ⊎ b ≡ '='
    help (mk&ₚ nil (some sndₚ₁) refl) b∈ = helpₚ b∈ sndₚ₁
    help (mk&ₚ (consIList (mk&ₚ (Base64.mk64 c c∈ i refl) (mk&ₚ (Base64.mk64 _ _ _ refl) (mk&ₚ (Base64.mk64 _ _ _ refl) (Base64.mk64 _ _ _ refl) refl) refl) refl) tail refl) sndₚ₁ bs≡) (here refl) =
      inj₁ (uneraseDec (subst (_∈ B64.charset) (sym (∷-injectiveˡ bs≡)) c∈) (_ ∈? _))
    help (mk&ₚ (consIList (mk&ₚ (Base64.mk64 _ _ _ refl) (mk&ₚ (Base64.mk64 _ c∈ _ refl) (mk&ₚ (Base64.mk64 _ _ _ refl) (Base64.mk64 _ _ _ refl) refl) refl) refl) tail refl) sndₚ₁ bs≡) (there (here refl)) =
      inj₁ (uneraseDec (subst (_∈ B64.charset) (sym (∷-injectiveˡ (∷-injectiveʳ bs≡))) c∈) (_ ∈? _))
    help (mk&ₚ (consIList (mk&ₚ (Base64.mk64 _ _ _ refl) (mk&ₚ (Base64.mk64 _ _ _ refl) (mk&ₚ (Base64.mk64 _ c∈ _ refl) (Base64.mk64 _ _ _ refl) refl) refl) refl) tail refl) sndₚ₁ bs≡) (there (there (here refl))) =
      inj₁ (uneraseDec (subst (_∈ B64.charset) (sym (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ bs≡)))) c∈) (_ ∈? _))
    help (mk&ₚ (consIList (mk&ₚ (Base64.mk64 _ _ _ refl) (mk&ₚ (Base64.mk64 _ _ _ refl) (mk&ₚ (Base64.mk64 _ _ _ refl) (Base64.mk64 _ c∈ _ refl) refl) refl) refl) tail refl) sndₚ₁ bs≡) (there (there (there (here refl)))) =
      inj₁ (uneraseDec (subst (_∈ B64.charset) (sym (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ (∷-injectiveʳ bs≡))))) c∈) (_ ∈? _))
    help (mk&ₚ (consIList (mk&ₚ (Base64.mk64 _ _ _ refl) (mk&ₚ (Base64.mk64 _ _ _ refl) (mk&ₚ (Base64.mk64 _ _ _ refl) (Base64.mk64 _ _ _ refl) refl) refl) refl) tail refl) sndₚ₁ bs≡) (there (there (there (there b∈)))) =
      help (mk&ₚ tail sndₚ₁ ((∷-injectiveʳ (∷-injectiveʳ (∷-injectiveʳ (∷-injectiveʳ bs≡))))) ) b∈

  -- TODO: equality for List Char is decidable, so guard against ≡ [] first and then handle the negation case separately
  noOverlap : NoOverlap Repₛ (Sum Base64.Base64Pad1 Base64.Base64Pad2)
  noOverlap ws xs₁ ys₁ xs₂ ys₂ ++≡ v₁ v₂ = noOverlapWF ws xs₁ ys₁ xs₂ ys₂ ++≡ v₁ v₂ (<-wellFounded _)
    where
    open import Data.Nat.Induction
      using (<-wellFounded)
    module ≤ = Nat.≤-Reasoning

    noOverlapWF
      : ∀ ws xs₁ ys₁ xs₂ ys₂ → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂
        → Repₛ (ws ++ xs₁) → (v₂ : Repₛ ws) → @0 Acc _<_ (lengthIList v₂) → (xs₁ ≡ []) ⊎ (¬ Sum Base64.Base64Pad1 Base64.Base64Pad2 xs₂)
    noOverlapWF .[] .[] ys₁ xs₂ ys₂ ++≡ nil nil ac = inj₁ refl
    noOverlapWF .[] xs₁ ys₁ xs₂ ys₂ ++≡ (consIList{bs₂ = bs₂} (mk&ₚ (Base64.mk64 c₁ c₁∈ _ refl) (mk&ₚ (Base64.mk64 c₂ c₂∈ _ refl) (mk&ₚ (Base64.mk64 c₃ c₃∈ _ refl) (Base64.mk64 c₄ c₄∈ _ refl)  refl) refl) refl) tail₁ bs≡₁) nil ac =
      inj₂ λ where
        p → contradiction c₄∈ (Base64Pad.c₄∉ (subst₀! (Sum _ _) (Base64Pad.forcebs p ++≡ bs≡₁) p))
    noOverlapWF ws xs₁ ys₁ xs₂ ys₂ ++≡ v₁ (consIList{bs₂ = bs₂} (mk&ₚ (Base64.mk64 c₁ c₁∈ _ refl) (mk&ₚ (Base64.mk64 c₂ c₂∈ _ refl) (mk&ₚ (Base64.mk64 c₃ c₃∈ _ refl) (Base64.mk64 c₄ c₄∈ _ refl)  refl) refl) refl) tail₁ bs≡₁) (WellFounded.acc rs) =
      case (subst₀ (λ x → Repₛ (x ++ xs₁)) bs≡₁ v₁) ret (const _) of λ where
        (consIList{bs₂ = bs₂'} (mk&ₚ (Base64.mk64 c₁' c₁∈' _ refl) (mk&ₚ (Base64.mk64 c₂' c₂∈' _ refl) (mk&ₚ (Base64.mk64 c₃' c₃∈' _ refl) (Base64.mk64 c₄' c₄∈' _ refl)  refl) refl) refl) tail₁' bs≡₁') →
          let bs₂≡ : Erased (bs₂ ≡ drop 4 ws)
              bs₂≡ = ─ subst ((bs₂ ≡_) ∘ (drop 4)) (sym bs≡₁) refl

              bs₂'≡ : Erased (bs₂' ≡ drop 4 ws ++ xs₁)
              bs₂'≡ = ─ proj₂ (Lemmas.length-++-≡ _ _ (c₁ ∷ c₂ ∷ c₃ ∷ [ c₄ ]) _
                                (begin ((c₁' ∷ c₂' ∷ c₃' ∷ [ c₄' ]) ++ bs₂' ≡⟨ sym bs≡₁' ⟩
                                       c₁ ∷ c₂ ∷ c₃ ∷ [ c₄ ] ++ bs₂ ++ xs₁ ≡⟨ cong (λ x → (c₁ ∷ c₂ ∷ c₃ ∷ [ c₄ ]) ++ x ++ xs₁) (Erased.x bs₂≡) ⟩
                                       c₁ ∷ c₂ ∷ c₃ ∷ [ c₄ ] ++ (drop 4 ws) ++ xs₁ ∎))
                                refl)

              v₂ : Repₛ (drop 4 ws)
              v₂ = subst₀! Repₛ (Erased.x bs₂≡) tail₁

              @0 <len : lengthIList v₂ < suc (lengthIList tail₁)
              <len =
                ≡-elim{x = ws} (λ {zs} eq → (eq' : bs₂ ≡ drop 4 zs) → lengthIList (subst₀! Repₛ (subst (λ x → bs₂ ≡ drop 4 zs) (sym eq) eq') tail₁) < suc (lengthIList tail₁))
                  (λ where
                    refl → Nat.≤-refl)
                  {y = ws} refl (¡ bs₂≡)
          in
          noOverlapWF (drop 4 ws) xs₁ ys₁ xs₂ ys₂ ++≡
            (subst₀! Repₛ (Erased.x bs₂'≡) tail₁') v₂
            (rs _ <len)

  fromExactLength : ∀ {@0 bs} {n} → {t : True (n % 4 ≟ 0)} → ExactLength (IList Base64.Base64Char) n bs → Base64.Base64Str bs
  fromExactLength (mk×ₚ  nil (─ len≡)) = Base64.mk64Str nil refl (Base64.Base64Pad.pad0 refl) refl
  fromExactLength{t = t} (mk×ₚ (consIList (Base64.mk64 c _ _ refl) nil refl) (─ len≡)) =
    contradiction (toWitness t) (subst₀ (¬_ ∘ (_≡ 0) ∘ (_% 4)) len≡ (λ ()))
  fromExactLength{t = t} (mk×ₚ (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 _ _ _ refl) nil refl) refl) (─ len≡)) =
    contradiction (toWitness t) (subst₀ (¬_ ∘ (_≡ 0) ∘ (_% 4)) len≡ (λ ()))
  fromExactLength{t = t} (mk×ₚ (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 _ _ _ refl) nil refl) refl) refl) (─ len≡)) =
    contradiction (toWitness t) (subst₀ (¬_ ∘ (_≡ 0) ∘ (_% 4)) len≡ (λ ()))
  fromExactLength{n = suc (suc (suc (suc n)))} {t = t} (mk×ₚ (consIList c₁@(Base64.mk64 _ _ _ refl) (consIList c₂@(Base64.mk64 _ _ _ refl) (consIList c₃@(Base64.mk64 _ _ _ refl) (consIList c₄@(Base64.mk64 _ _ _ refl) t₄ refl) refl) refl) refl) (─ len≡)) =
    case fromExactLength{n = n}{t = t} (mk×ₚ t₄ (─ Nat.+-cancelˡ-≡ 4 len≡))  ret (const _) of λ where
      (Base64.mk64Str str strLen pad refl) →
        Base64.mk64Str (consIList c₁ (consIList c₂ (consIList c₃ (consIList c₄ str refl) refl) refl) refl )
          strLen
          pad refl

  b64Str? : Decidable (λ x → Base64.Base64Str x)
  b64Str? bs =
    case length bs % 4 ≟ 0 of λ where
      (no ¬≡0) →
        no λ where
          (Base64.mk64Str{s = s}{p} str strLen pad bs≡) →
            contradiction
              (subst ((_≡ 0) ∘ (_% 4) ∘ length) (sym bs≡)
                (begin length (s ++ p) % 4               ≡⟨ cong (_% 4) (length-++ s) ⟩
                       (length s + length p) % 4         ≡⟨ Nat.%-distribˡ-+ (length s) _ 4 ⟩
                       (length s % 4 + length p % 4) % 4 ≡⟨ cong (λ x → (length s % 4 + x) % 4) (Base64Pad.p%4≡0 pad) ⟩
                       (length s % 4 + 0) % 4            ≡⟨ cong (_% 4) (Nat.+-identityʳ (length s % 4)) ⟩
                       (length s % 4) % 4                ≡⟨ m%n%n≡m%n (length s) _ ⟩
                       length s % 4                      ≡⟨ strLen ⟩
                       0                                 ∎))
              ¬≡0
      (yes ≡0) → helper bs ≡0
    where
    helper : ∀ bs → @0 length bs % 4 ≡ 0 → Dec (Base64.Base64Str bs)
    helper [] %4 = yes (Base64.mk64Str nil refl (Base64.pad0 refl) refl)
    helper (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ []) refl
      with c₁ ∈? B64.charset
      |    c₂ ∈? B64.charset
    ... | no c₁∉ | _ =
      no λ where
        (Base64.mk64Str nil strLen (Base64.pad0 refl) ())
        (Base64.mk64Str nil strLen (Base64.pad1 (Base64.mk64P1 (Base64.mk64 .c₁ c∈ i refl) c₂' c₃' pad refl)) refl) →
          contradiction c∈ c₁∉
        (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P2 (Base64.mk64 .c₁ c∈ i refl) c₂ pad refl)) refl) →
          contradiction c∈ c₁∉
        (Base64.mk64Str (cons (mkIListCons (Base64.mk64 c c∈ i refl) tail₁ refl)) strLen pad bs≡) →
          contradiction (subst (_∈ B64.charset) (∷-injectiveˡ (sym bs≡)) c∈) c₁∉
    ... | yes _  | no c₂∉ =
      no λ where
        (Base64.mk64Str nil strLen (Base64.pad0 ()) refl)
        (Base64.mk64Str nil strLen (Base64.pad1 (Base64.mk64P1 (Base64.mk64 _ _ _ refl) (Base64.mk64 c₂' c₂∈' i₂' refl) c₃ pad refl)) bs≡) →
          contradiction (subst (_∈ B64.charset) (∷-injectiveˡ (∷-injectiveʳ (sym bs≡))) c₂∈') c₂∉
        (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P2 (Base64.mk64 ._ _ _ refl) (Base64.mk64 .c₂ c₂∈' i₁ refl) pad refl)) refl) →
          contradiction c₂∈' c₂∉
        (Base64.mk64Str (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 c₂' c₂∈' _ refl) tail₁ refl) refl) strLen pad bs≡) →
          contradiction (subst (_∈ B64.charset) (∷-injectiveˡ (∷-injectiveʳ (sym bs≡))) c₂∈') c₂∉
    ... | yes c₁∈ | yes c₂∈
      with c₃ ∈? B64.charset
    ... | no ¬c₃∈ =
      case (c₃ ≟ '=') ,′ (c₄ ≟ '=') of λ where
        (no ¬c₃≡= , _) →
          no λ where
            (Base64.mk64Str nil strLen (Base64.pad0 refl) ())
            (Base64.mk64Str nil strLen (Base64.pad1 (Base64.mk64P1 (Base64.mk64 .c₁ c₁∈' _ refl) (Base64.mk64 .c₂ c₂∈' _ refl) (Base64.mk64 .c₃ c₃∈' _ refl) pad refl)) refl) →
              contradiction c₃∈' ¬c₃∈
            (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P2 (Base64.mk64 .c₁ c∈ i refl) (Base64.mk64 .c₂ c∈₁ i₁ refl) pad refl)) refl) →
              contradiction (erefl '=') ¬c₃≡=
            (Base64.mk64Str (consIList (Base64.mk64 c₁' _ _ refl) (consIList (Base64.mk64 c₂' _ _ refl) (consIList (Base64.mk64 c₃' c₃'∈ _ refl) _ refl) refl) refl) strLen pad bs≡) →
              contradiction (subst (_∈ B64.charset) (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ (sym bs≡)))) c₃'∈) ¬c₃∈
        (yes refl , no ¬c₄≡=) →
          no λ where
            (Base64.mk64Str nil strLen (Base64.pad0 refl) ())
            (Base64.mk64Str nil strLen (Base64.pad1 (Base64.mk64P1 (Base64.mk64 .c₁ c∈ i refl) (Base64.mk64 .c₂ c∈₁ i₁ refl) (Base64.mk64 .'=' c∈₂ i₂ refl) pad refl)) refl) →
              contradiction (erefl '=') ¬c₄≡=
            (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P2 (Base64.mk64 .c₁ c∈ i refl) (Base64.mk64 .c₂ c∈₁ i₁ refl) pad refl)) refl) →
              contradiction (erefl '=') ¬c₄≡=
            (Base64.mk64Str (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 c₃' c₃∈' _ refl) (consIList (Base64.mk64 c₄' c₄∈' _ refl) _ refl) refl) refl) refl) strLen pad bs≡) →
              contradiction c₃∈' (subst (¬_ ∘ (_∈ B64.charset)) (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ bs≡))) (toWitnessFalse {Q = _ ∈? _} tt))
        (yes refl , yes refl) →
          let i = Any.index c₂∈ in
          case toℕ i % (2 ^ 4) ≟ 0 of λ where
            (no ¬c₂0s) →
              no λ where
                (Base64.mk64Str nil strLen (Base64.pad0 refl) ())
                (Base64.mk64Str nil strLen (Base64.pad1 (Base64.mk64P1 (Base64.mk64 .c₁ c∈ i refl) (Base64.mk64 .c₂ c∈₁ i₁ refl) (Base64.mk64 .'=' c₃∈' _ refl) pad refl)) refl) →
                  contradiction c₃∈' (toWitnessFalse{Q = _ ∈? _} tt)
                (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P2 (Base64.mk64 .c₁ _ _ refl) (Base64.mk64 .c₂ c₂∈' (singleton i' i≡') refl) pad refl)) refl) →
                  contradiction
                    (begin toℕ (Any.index c₂∈)  % (2 ^ 4) ≡⟨ cong (λ x → toℕ (Any.index x) % (2 ^ 4)) (B64.∈charsetUnique c₂∈ c₂∈') ⟩
                           toℕ (Any.index c₂∈') % (2 ^ 4) ≡⟨ cong (λ x → toℕ x % (2 ^ 4)) (sym i≡') ⟩
                           toℕ i' % (2 ^ 4)               ≡⟨ pad ⟩
                           0 ∎)
                    ¬c₂0s
                (Base64.mk64Str (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 _ _ _ refl) (cons (mkIListCons (Base64.mk64 c₃' c₃∈' _ refl) _ refl)) refl) refl) strLen pad bs≡) →
                  contradiction c₃∈' (subst (¬_ ∘ (_∈ B64.charset)) (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ bs≡))) (toWitnessFalse{Q = _ ∈? _} tt))
            (yes c₂0s) →
              yes (Base64.mk64Str nil refl (Base64.pad2 (Base64.mk64P2 (Base64.mk64 c₁ c₁∈ self refl) (Base64.mk64 c₂ c₂∈ self refl) c₂0s refl)) refl)
    ... | yes c₃∈
      with c₄ ∈? B64.charset
    ... | no ¬c₄∈ =
      case c₄ ≟ '=' of λ where
        (no ¬c₄≡=) →
          no λ where
            (Base64.mk64Str nil strLen (Base64.pad0 refl) ())
            (Base64.mk64Str nil strLen (Base64.pad1 (Base64.mk64P1 (Base64.mk64 .c₁ c∈ i refl) (Base64.mk64 .c₂ c∈₁ i₁ refl) (Base64.mk64 .c₃ c∈₂ i₂ refl) pad refl)) refl) →
              contradiction refl ¬c₄≡=
            (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P2 (Base64.mk64 .c₁ c∈ i refl) (Base64.mk64 .c₂ c∈₁ i₁ refl) pad refl)) refl) →
              contradiction refl ¬c₄≡=
            (Base64.mk64Str (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 c₄' c₄∈' _ refl) _ refl) refl) refl) refl) strLen pad bs≡) →
              contradiction (subst (_∈ B64.charset) (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ (∷-injectiveʳ (sym bs≡))))) c₄∈') ¬c₄∈
        (yes refl) →
          let i = Any.index c₃∈ in
          case toℕ i % (2 ^ 2) ≟ 0 of λ where
            (no ¬c₃0s) →
              no λ where
                (Base64.mk64Str nil strLen (Base64.pad0 refl) ())
                (Base64.mk64Str nil strLen (Base64.pad1 (Base64.mk64P1 (Base64.mk64 _ _ _ refl) (Base64.mk64 _ _ _ refl) (Base64.mk64 _ c₃∈' (singleton i' i≡') refl) pad refl)) refl) →
                  contradiction
                    (begin toℕ (Any.index c₃∈)  % (2 ^ 2) ≡⟨ cong (λ x → toℕ (Any.index x) % (2 ^ 2)) (B64.∈charsetUnique c₃∈ c₃∈') ⟩
                           toℕ (Any.index c₃∈') % (2 ^ 2) ≡⟨ cong (λ x → toℕ x % (2 ^ 2)) (sym i≡') ⟩
                           toℕ i' % (2 ^ 2) ≡⟨ pad ⟩
                           0 ∎)
                    ¬c₃0s
                (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P2 (Base64.mk64 .c₁ c∈ i refl) (Base64.mk64 .c₂ c∈₁ i₁ refl) pad refl)) refl) →
                  contradiction c₃∈ (toWitnessFalse{Q = _ ∈? _} tt)
                (Base64.mk64Str (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 c₄' c₄∈' _ refl) tail₁ refl) refl) refl) refl) strLen pad bs≡) →
                  contradiction (subst (_∈ B64.charset) (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ (∷-injectiveʳ (sym bs≡))))) c₄∈') ¬c₄∈
            (yes c₃0s) →
              yes (Base64.mk64Str nil refl (Base64.pad1 (Base64.mk64P1 (Base64.mk64 c₁ c₁∈ self refl) (Base64.mk64 c₂ c₂∈ self refl) (Base64.mk64 c₃ c₃∈ self refl) c₃0s refl)) refl)
    ... | yes c₄∈ =
      yes (Base64.mk64Str (consIList (Base64.mk64 c₁ c₁∈ self refl) (consIList (Base64.mk64 c₂ c₂∈ self refl) (consIList (Base64.mk64 c₃ c₃∈ self refl) (consIList (Base64.mk64 c₄ c₄∈ self refl) nil refl) refl) refl) refl) refl (Base64.pad0 refl) (sym (++-identityʳ _)))
    helper (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs@(_ ∷ _)) %4
      with helper bs %4
    ... | no ¬p =
      no λ where
        (Base64.mk64Str nil strLen (Base64.pad0 refl) ())
        (Base64.mk64Str nil strLen (Base64.pad1 (Base64.mk64P1 c₁ c₂ c₃ pad refl)) ())
        (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P2 c₁ c₂ pad refl)) ())
        (Base64.mk64Str (consIList (Base64.mk64 c₁' c₁∈' i₁' refl) (consIList (Base64.mk64 c₂' c₂∈' i₂' refl) (consIList (Base64.mk64 c₃' c₃∈' i₃' refl) (consIList (Base64.mk64 c₄' c₄∈' i₄' refl) tail₁ refl) refl) refl) refl) strLen pad bs≡) →
          contradiction
            (Base64.mk64Str tail₁ strLen pad (proj₂ $ Lemmas.length-++-≡ (_ ∷ _ ∷ _ ∷ [ _ ]) bs (_ ∷ _ ∷ _ ∷ [ _ ]) _ bs≡ (erefl 4)))
            ¬p
    helper (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs@(_ ∷ _)) %4 | yes (Base64.mk64Str str₀ strLen₀ pad₀ bs≡₀)
      with All.all? (_∈? B64.charset) (c₁ ∷ c₂ ∷ c₃ ∷ [ c₄ ])
    ... | no ¬all∈ =
      no λ where
        (Base64.mk64Str nil strLen (Base64.pad0 refl) ())
        (Base64.mk64Str nil strLen (Base64.pad1 (Base64.mk64P1 c₁ c₂ c₃ pad ())) refl)
        (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P2 c₁ c₂ pad refl)) ())
        (Base64.mk64Str (consIList (Base64.mk64 c₁' c₁∈' i₁' refl) (consIList (Base64.mk64 c₂' c₂∈' i₂' refl) (consIList (Base64.mk64 c₃' c₃∈' i₃' refl) (consIList (Base64.mk64 c₄' c₄∈' i₄' refl) tail₁ refl) refl) refl) refl) strLen pad bs≡) →
          contradiction
            (subst (All (_∈ B64.charset))
              (proj₁ $ Lemmas.length-++-≡ _ _ _ _ (sym bs≡) refl)
              (c₁∈' All.∷ c₂∈' All.∷ c₃∈' All.∷ c₄∈' All.∷ All.[]))
            ¬all∈
    ... | yes (c₁∈ All.∷ c₂∈ All.∷ c₃∈ All.∷ c₄∈ All.∷ All.[]) = yes $
      Base64.mk64Str
        (consIList (Base64.mk64 c₁ c₁∈ self refl)
          (consIList (Base64.mk64 c₂ c₂∈ self refl)
            (consIList (Base64.mk64 c₃ c₃∈ self refl)
              (consIList (Base64.mk64 c₄ c₄∈ self refl) str₀ refl) refl) refl) refl)
        strLen₀ pad₀
        (cong (λ x → c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ x) bs≡₀)

  @0 unambiguous : Unambiguous Base64.Base64Str
  unambiguous a₁ a₂ = uaWF a₁ a₂ (Nat.<-wellFounded _)
    where
    import Data.Nat.Induction as Nat

    @0 uaWF : ∀ {xs} → (a₁ a₂ : Base64.Base64Str xs) → @0 Acc _<_ (lengthIList (Base64.Base64Str.str a₁))
           → a₁ ≡ a₂
    uaWF (Base64.mk64Str nil refl pad₁ refl) (Base64.mk64Str nil refl pad₂ refl) ac =
      case Base64Pad.unambiguous pad₁ pad₂ of λ where
        refl → refl
    uaWF (Base64.mk64Str nil strLen₁ (Base64.pad0 ()) refl) (Base64.consBase64Str i₁ i₂ i₃ {c₄∈ = c₄∈}i₄ str₂ strLen₂ pad₂ refl) ac
    uaWF (Base64.mk64Str nil strLen₁ Base64.mk64P1! refl) (Base64.consBase64Str i₁ i₂ i₃ {c₄∈ = c₄∈}i₄ str₂ strLen₂ pad₂ bs≡₂) ac =
      contradiction{P = '=' ∈ B64.charset} (subst (_∈ B64.charset) (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ (∷-injectiveʳ (sym bs≡₂))))) c₄∈) (toWitnessFalse{Q = _ ∈? _} tt)
    uaWF (Base64.mk64Str nil strLen₁ Base64.mk64P2! refl) (Base64.consBase64Str i₁ i₂ {c₃∈ = c₃∈}i₃ i₄ str₂ strLen₂ pad₂ bs≡₂) ac =
      contradiction {P = '=' ∈ B64.charset} (subst (_∈ B64.charset) (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ (sym bs≡₂)))) c₃∈) (toWitnessFalse{Q = _ ∈? _} tt)
    uaWF (Base64.consBase64Str i₁ i₂ i₃ i₄ str₁ strLen₁ pad₁ refl) (Base64.mk64Str nil strLen₂ (Base64.pad0 ()) refl) ac
    uaWF (Base64.consBase64Str i₁ i₂ i₃ {c₄∈ = c₄∈}i₄ str₁ strLen₁ pad₁ refl) (Base64.mk64Str nil strLen₂ Base64.mk64P1! bs≡₂) ac =
      contradiction{P = '=' ∈ B64.charset} (subst (_∈ B64.charset) (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ (∷-injectiveʳ bs≡₂)))) c₄∈) (toWitnessFalse{Q = _ ∈? _} tt)
    uaWF (Base64.consBase64Str i₁ i₂ {c₃∈ = c₃∈}i₃ i₄ str₁ strLen₁ pad₁ refl) (Base64.mk64Str nil strLen₂ Base64.mk64P2! bs≡₂) ac =
      contradiction {P = '=' ∈ B64.charset} (subst (_∈ B64.charset) (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ bs≡₂))) c₃∈) (toWitnessFalse{Q = _ ∈? _} tt)
    uaWF (Base64.consBase64Str {c₁₁} i₁₁ {c₁₂} i₁₂ {c₁₃} i₁₃ {c₁₄} i₁₄ str₁ strLen₁ pad₁ refl) (Base64.consBase64Str {c₂₁} i₂₁ {c₂₂} i₂₂ {c₂₃} i₂₃ {c₂₄} i₂₄ str₂ strLen₂ pad₂ bs≡₂) (WellFounded.acc rs) =
      case proj₁ bs≡× of λ where
        refl →
          (case (─ (  Base64Char.unambiguous (Base64.mk64!{c₁₁} i₁₁) (Base64.mk64!{c₂₁} i₂₁)
                  ,′ Base64Char.unambiguous (Base64.mk64!{c₁₂} i₁₂) (Base64.mk64!{c₂₂} i₂₂)
                  ,′ Base64Char.unambiguous (Base64.mk64!{c₁₃} i₁₃) (Base64.mk64!{c₂₃} i₂₃)
                  ,′ Base64Char.unambiguous (Base64.mk64!{c₁₄} i₁₄) (Base64.mk64!{c₂₄} i₂₄)))
          ret (const (typeOf (proj₂ bs≡×) → _))
          of λ where
            (─ (refl , refl , refl , refl)) eq →
              case ‼ uaWF (Base64.mk64Str str₁ strLen₁ pad₁ refl) (Base64.mk64Str str₂ strLen₂ pad₂ eq) (rs _ (s≤s (Nat.m≤n+m _ 3))) ret (const _) of λ where
                refl → ‼ (case ≡-unique refl bs≡₂ of λ where
                  refl → refl))
            (‼ proj₂ bs≡×)

      where
      bs≡× : (c₁₁ ∷ c₁₂ ∷ c₁₃ ∷ [ c₁₄ ] ≡ c₂₁ ∷ c₂₂ ∷ c₂₃ ∷ [ c₂₄ ]) × _ ≡ _
      bs≡× = Lemmas.length-++-≡ _ _ _ _ bs≡₂ refl
