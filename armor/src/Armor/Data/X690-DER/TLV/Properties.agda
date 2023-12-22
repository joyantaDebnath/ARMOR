open import Armor.Prelude
open import Armor.Binary
open import Armor.Data.X690-DER.Length
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Grammar.Definitions
open import Armor.Grammar.Parallel.TCB UInt8
import      Armor.Grammar.Parallel.Properties UInt8 as Parallel
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X690-DER.TLV.Properties where

open Armor.Grammar.Definitions              UInt8

nonempty : ∀ {t} {A : @0 List UInt8 → Set} → NonEmpty (TLV t A)
nonempty (mkTLV len val len≡ ()) refl

@0 nosubstrings : ∀ {t} {A : @0 List UInt8 → Set} → NoSubstrings (TLV t A)
nosubstrings{t}{xs₁ = xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ (mkTLV{l}{v} len val len≡ bs≡) (mkTLV{l₁}{v₁} len₁ val₁ len≡₁ bs≡₁) =
  ‼ (begin xs₁ ≡⟨ bs≡ ⟩
           t ∷ l ++ v ≡⟨ cong (t ∷_) (cong (_++ v) l≡) ⟩
           t ∷ l₁ ++ v ≡⟨ cong (t ∷_) (cong (l₁ ++_) v≡) ⟩
           t ∷ l₁ ++ v₁ ≡⟨ sym bs≡₁ ⟩
           xs₂ ∎)
  where
  open ≡-Reasoning
  @0 l++≡ : l ++ v ++ ys₁ ≡ l₁ ++ v₁ ++ ys₂
  l++≡ = ∷-injectiveʳ (begin (t ∷ l ++ v ++ ys₁     ≡⟨ cong (t ∷_) (solve (++-monoid UInt8)) ⟩
                              t ∷ (l ++ v) ++ ys₁   ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
                              xs₁ ++ ys₁            ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
                              xs₂ ++ ys₂            ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
                              t ∷ (l₁ ++ v₁) ++ ys₂ ≡⟨ cong (t ∷_) (solve (++-monoid UInt8)) ⟩
                              t ∷ l₁ ++ v₁ ++ ys₂   ∎))

  @0 l≡ : l ≡ l₁
  l≡ = Length.nosubstrings l++≡ len len₁

  @0 v≡ : v ≡ v₁
  v≡ = proj₁ $ Lemmas.length-++-≡ _ _ _ _
                 (++-cancelˡ l (trans l++≡ (cong (_++ v₁ ++ ys₂) (sym l≡))))
                 (begin length v       ≡⟨ sym len≡ ⟩
                        getLength len  ≡⟨ Length.unambiguous-getLength l≡ len len₁ ⟩
                        getLength len₁ ≡⟨ len≡₁ ⟩
                        length v₁      ∎)

@0 noconfusion : ∀ {A₁ A₂ : @0 List UInt8 → Set} {t₁ t₂} → t₁ ≢ t₂ → NoConfusion (TLV t₁ A₁) (TLV t₂ A₂)
noconfusion t₁≢t₂{xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ (mkTLV len val len≡ bs≡) (mkTLV len₁ val₁ len≡₁ bs≡₁) =
 contradiction (∷-injectiveˡ (trans (cong (_++ ys₁) (sym bs≡)) (trans xs₁++ys₁≡xs₂++ys₂ (cong (_++ ys₂) bs≡₁)))) t₁≢t₂

@0 noconfusionVal
  : ∀ {t} {A B : @0 List UInt8 → Set} → @0 NoConfusion A B
    → NoConfusion (TLV t A) (TLV t B)
noconfusionVal{t} nc {xs₁}{ys₁}{xs₂}{ys₂}xs₁++ys₁≡xs₂++ys₂ (mkTLV{l}{v} len val len≡ bs≡) (mkTLV{l'}{v'} len₁ val₁ len≡₁ bs≡₁) =
  nc ++≡“ val val₁
  where
  open ≡-Reasoning

  @0 ++≡' : l ++ v ++ ys₁ ≡ l' ++ v' ++ ys₂
  ++≡' = ∷-injectiveʳ (begin
    t ∷ l ++ v ++ ys₁ ≡⟨ cong (t ∷_) (sym (++-assoc l v ys₁)) ⟩
    (t ∷ l ++ v) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
    xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
    xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
    (t ∷ l' ++ v') ++ ys₂ ≡⟨ cong (t ∷_) (++-assoc l' v' ys₂) ⟩
    t ∷ l' ++ v' ++ ys₂ ∎)

  @0 l≡ : l ≡ l'
  l≡ = Length.nosubstrings ++≡' len len₁

  @0 ++≡“ : v ++ ys₁ ≡ v' ++ ys₂
  ++≡“ = Lemmas.++-cancel≡ˡ _ _ l≡
    (begin l ++ v ++ ys₁ ≡⟨ ++≡' ⟩
           l' ++ v' ++ ys₂ ∎)

private
  module TLVProps where
    @0 unambiguous : ∀ {t} {A : @0 List UInt8 → Set} → Unambiguous A → Unambiguous (TLV t A)
    unambiguous{t}{A} ua (mkTLV{l = l₁}{v₁} len₁ val₁ len≡₁ bs≡₁) (mkTLV{l = l₂}{v₂} len₂ val₂ len≡₂ bs≡₂) =
      subst₀ (λ l₂ → ∀ (len₂ : Length l₂) len≡₂ bs≡₂ → mkTLV len₁ val₁ len≡₁ bs≡₁ ≡ mkTLV {l = l₂} len₂ val₂ len≡₂ bs≡₂ ) l≡
        (λ len₂ len≡₂ bs≡₂' →
          subst₀ (λ v₂ → ∀ (val₂ : A v₂) len≡₂ bs≡₂ → mkTLV len₁ val₁ len≡₁ bs≡₁ ≡ mkTLV len₂ val₂ len≡₂ bs≡₂) v≡
            (λ val₂ len≡₂ bs≡₂' →
              subst₂ (λ len₂ val₂ → ∀ len≡₂ → mkTLV len₁ val₁ len≡₁ bs≡₁ ≡ mkTLV len₂ val₂ len≡₂ bs≡₂')
                (Length.unambiguous len₁ len₂) (ua val₁ val₂)
                (λ len≡₂ →
                  subst₂ (λ x y → _ ≡ mkTLV len₁ val₁ x y) (≡-unique len≡₁ len≡₂) (≡-unique bs≡₁ bs≡₂')
                    refl)
                len≡₂ )
            val₂ len≡₂ bs≡₂')
        len₂ len≡₂ bs≡₂
      where
      @0 bs≡' : l₁ ++ v₁ ≡ l₂ ++ v₂
      bs≡' = ∷-injectiveʳ (trans₀ (sym bs≡₁) bs≡₂)
    
      @0 l≡ : l₁ ≡ l₂
      l≡ = Length.nosubstrings bs≡' len₁ len₂
    
      @0 v≡ : v₁ ≡ v₂
      v≡ = Lemmas.++-cancel≡ˡ _ _ l≡ bs≡'
  
    valBS≡ : ∀ {@0 A} {@0 t bs₁ bs₂} → @0 bs₁ ≡ bs₂
             → (v₁ : TLV t A bs₁) (v₂ : TLV t A bs₂)
             → TLV.v v₁ ≡ TLV.v v₂
    valBS≡{t = t} refl (mkTLV{l}{v} len val len≡ bs≡) (mkTLV{l₁}{v₁} len₁ val₁ len≡₁ bs≡₁) =
      Lemmas.++-cancel≡ˡ _ _ (‼ cong (t ∷_) (Length.nosubstrings (∷-injectiveʳ bs≡') len len₁)) (‼ bs≡')
      where
      @0 bs≡' : t ∷ l ++ v ≡ t ∷ l₁ ++ v₁
      bs≡' = trans (sym bs≡) bs≡₁

module NonEmptyVal where
  @0 unambiguous : ∀ {t} {A : @0 List UInt8 → Set} → Unambiguous A → Unambiguous (Σₚ (TLV t A) TLVNonEmptyVal)
  unambiguous ua = Parallel.unambiguous (TLVProps.unambiguous ua) λ _ → ≤-irrelevant

open TLVProps public

instance
  EqTLV : ∀ {A : @0 List UInt8 → Set} ⦃ _ : Eq≋ A ⦄ → ∀ {t} → Eq≋ (TLV t A)
  Eq≋._≋?_ (EqTLV{t = t}) {bs₁} {bs₂} t₁ t₂
    with TLV.len t₁ ≋? TLV.len t₂
    |    TLV.val t₁ ≋? TLV.val t₂
  ... | no ¬len₁≋len₂ | _ = no λ where
    (mk≋ refl refl) → contradiction ≋-refl ¬len₁≋len₂
  ... | yes ≋-refl | no ¬v₁≋v₂ = no λ where
    ≋-refl → contradiction ≋-refl ¬v₁≋v₂
  ... | yes ≋-refl | yes ≋-refl
    with ‼ ≡-unique (TLV.len≡ t₁) (TLV.len≡ t₂)
  ... | refl
    with ‼ bs₁≡bs₂
    where
    @0 bs₁≡bs₂ : bs₁ ≡ bs₂
    bs₁≡bs₂ = trans (TLV.bs≡ t₁) (sym (TLV.bs≡ t₂))
  ... | refl
    with ‼ ≡-unique (TLV.bs≡ t₁) (TLV.bs≡ t₂)
  ... | refl = yes ≋-refl

  eqTLV : ∀ {A : @0 List UInt8 → Set} {t} ⦃ _ : Eq (Exists─ (List UInt8) A) ⦄ → Eq (Exists─ (List UInt8) (TLV t A))
  eqTLV{A} = Eq≋⇒Eq (EqTLV{A} ⦃ Eq⇒Eq≋ it ⦄)

@0 getLengthLen≡ : ∀ {t} {A : @0 List UInt8 → Set} {@0 xs₁ ys₁ xs₂ ys₂} → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂
                   → (v₁ : TLV t A xs₁) (v₂ : TLV t A xs₂) → getLength (TLV.len v₁) ≡ getLength (TLV.len v₂)
getLengthLen≡{t}{xs₁ = xs₁}{ys₁}{xs₂}{ys₂} ++≡ v₁ v₂
  with Length.nosubstrings (∷-injectiveʳ bs≡') (TLV.len v₁) (TLV.len v₂)
  where
  open ≡-Reasoning
  bs≡' : t ∷ TLV.l v₁ ++ TLV.v v₁ ++ ys₁ ≡ t ∷ TLV.l v₂ ++ TLV.v v₂ ++ ys₂
  bs≡' = begin
    t ∷ TLV.l v₁ ++ TLV.v v₁ ++ ys₁   ≡⟨ cong (t ∷_) (sym $ ++-assoc (TLV.l v₁) _ _) ⟩
    (t ∷ TLV.l v₁ ++ TLV.v v₁) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym $ TLV.bs≡ v₁) ⟩
    xs₁ ++ ys₁                                        ≡⟨ ++≡ ⟩
    xs₂ ++ ys₂                                        ≡⟨ cong (_++ ys₂) (TLV.bs≡ v₂) ⟩
    (t ∷ TLV.l v₂ ++ TLV.v v₂) ++ ys₂ ≡⟨ cong (t ∷_) (++-assoc (TLV.l v₂) _ _) ⟩
    t ∷ TLV.l v₂ ++ TLV.v v₂ ++ ys₂   ∎
... | refl = cong getLength (Length.unambiguous (TLV.len v₁) (TLV.len v₂))

@0 nonmalleable : ∀ {t} {A : @0 List UInt8 → Set} {R : Raw A} → NonMalleable R → NonMalleable (RawTLV t R)
nonmalleable{A = A} nm (mkTLV len val len≡ refl) (mkTLV len₁ val₁ len≡₁ refl) eq =
  case val≡val₁ ret (const _) of λ where
    refl → case (‼ Length.nonmalleable len len₁ (trans len≡ (sym len≡₁))) ret (const _) of λ where
      refl → case (‼ ≡-unique len≡ len≡₁) ret (const _) of λ where
        refl → refl
  where
  val≡val₁ : _≡_{A = Exists─ (List UInt8) A} (─ _ , val) (─ _ , val₁)
  val≡val₁ = nm val val₁ eq
