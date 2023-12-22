{-# OPTIONS --inversion-max-depth=300 #-}

open import Armor.Prelude
open import Armor.Binary
open import Armor.Data.X690-DER.Length.TCB
import      Armor.Grammar.Definitions
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X690-DER.Length.Properties where

open Armor.Grammar.Definitions              UInt8

elimMinRepLong
  : ∀ {ℓ} lₕ lₜ (P : UInt8 → List UInt8 → Set ℓ) →
    (lₜ ≡ [] → toℕ lₕ ≥ 128 → P lₕ lₜ) →
    (lₜ ≢ [] → P lₕ lₜ) →
    MinRepLong lₕ lₜ → P lₕ lₜ
elimMinRepLong lₕ lₜ P pf₁ pf₂ mr
  with lₜ ≟ []
... | no  lₜ≢[] = pf₂ lₜ≢[]
... | yes lₜ≡[] = pf₁ lₜ≡[] mr

uniqueMinRepLong : ∀ {lₕ lₜ} → Unique (MinRepLong lₕ lₜ)
uniqueMinRepLong{lₕ}{lₜ} p₁ p₂
  with lₜ ≟ []
... | no  lₜ≢[] = ⊤-unique p₁ p₂
... | yes lₜ≡[] = ≤-unique p₁ p₂

-- Smart constructors
shortₛ : ∀ l → {@0 _ : True (toℕ l <? 128)} → Length [ l ]
shortₛ l {l<128} = short (mkShort l (toWitness l<128) refl)

mkLongₛ : ∀ l lₕ lₜ →
        {@0 _ : True (128 <? toℕ l)}
        {@0 _ : True (toℕ lₕ >? 0)}
        {@0 _ : True (length lₜ ≟ (toℕ l - 129))}
        {@0 _ : True (lₜ ≠ [] ⊎-dec toℕ lₕ ≥? 128)}
        → Long (l ∷ lₕ ∷ lₜ)
mkLongₛ l lₕ lₜ {l>128} {lₕ≢0} {lₜLen} {mr} =
 (mkLong l
        (toWitness l>128) lₕ
        (toWitness lₕ≢0) lₜ
        (toWitness lₜLen) (go mr) refl)
 where
 go : True (lₜ ≠ [] ⊎-dec toℕ lₕ ≥? 128) → if ⌊ lₜ ≟ [] ⌋ then toℕ lₕ ≥ 128 else ⊤
 go mr
   with toWitness mr
 ... | inj₁ lₜ≢[]
   with lₜ ≟ []
 ... | no  _ = tt
 ... | yes lₜ≡[] = contradiction lₜ≡[] lₜ≢[]
 go mr | inj₂ y
   with lₜ ≟ []
 ... | no _ = tt
 ... | yes lₜ≡[] = y

longₛ : ∀ l lₕ lₜ →
      {@0 _ : True (128 <? toℕ l)}
      {@0 _ : True (toℕ lₕ >? 0)}
      {@0 _ : True (length lₜ ≟ (toℕ l - 129))}
      {@0 _ : True (lₜ ≠ [] ⊎-dec toℕ lₕ ≥? 128)}
          → Length (l ∷ lₕ ∷ lₜ)
longₛ l lₕ lₜ {l>128} {lₕ≢0} {lₜLen} {mr} =
  long (mkLongₛ l lₕ lₜ {l>128} {lₕ≢0} {lₜLen} {mr})

-- examples
_ : Length _
_ = shortₛ (# 3)

_ : Length _
_ = longₛ (# 130) (# 1) [ # 1 ]

@0 unambiguous : Unambiguous Length
unambiguous (short (mkShort l l<128 refl)) (short (mkShort .l l<129 refl)) =
  case ≤-irrelevant l<128 l<129 of λ where
    refl → refl
unambiguous (short (mkShort l l<128 refl)) (long (mkLong l₁ l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep ()))
unambiguous (long (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl)) (short (mkShort l₁ l<128 ()))
unambiguous (long (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl)) (long (mkLong .l l>129 .lₕ lₕ≢1 .lₜ lₜLen₁ lₕₜMinRep₁ refl)) =
  case _ × _ × _ × _ ∋ ≤-irrelevant l>128 l>129 , ≤-irrelevant lₕ≢0 lₕ≢1 , ≡-unique lₜLen lₜLen₁ , uniqueMinRepLong lₕₜMinRep lₕₜMinRep₁ of λ where
    (refl , refl , refl , refl) → refl

@0 unambiguous-getLength : ∀ {xs ys} → xs ≡ ys → (l₁ : Length xs) (l₂ : Length ys) → getLength l₁ ≡ getLength l₂
unambiguous-getLength refl l₁ l₂ = cong getLength (unambiguous l₁ l₂)

instance
  Length≋ : Eq≋ Length
  Eq≋._≋?_ Length≋ {bs₁} {bs₂} (short (mkShort l l<128 bs≡)) (short (mkShort l₁ l<129 bs≡₁))
    with l ≟ l₁
  ... | no ¬p = no λ where
    (mk≋ refl refl) → contradiction refl ¬p
  Eq≋._≋?_ Length≋ l₁@(short (mkShort l l<128 refl)) l₂@(short (mkShort .l l<129 refl)) | yes refl =
    yes (mk≋ refl (unambiguous l₁ l₂))
  Eq≋._≋?_ Length≋ {bs₁} {bs₂} (short x) (long x₁) = no λ where (mk≋ refl ())
  Eq≋._≋?_ Length≋ {bs₁} {bs₂} (long x) (short x₁) = no λ where (mk≋ refl ())
  Eq≋._≋?_ Length≋ {bs₁} {bs₂} (long (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep bs≡)) (long (mkLong l₁ l>129 lₕ₁ lₕ≢1 lₜ₁ lₜLen₁ lₕₜMinRep₁ bs≡₁))
    with l ∷ lₕ ∷ lₜ ≟ l₁ ∷ lₕ₁ ∷ lₜ₁
  ... | no ¬p = no λ where
    (Armor.Grammar.Definitions.mk≋ refl refl) → contradiction refl ¬p
  Eq≋._≋?_ Length≋ l₁@(long (mkLong l _ _ _ _ _ _ refl)) l₂@(long (mkLong .l _ ._ _ ._ _ _ refl)) | yes refl =
    yes (mk≋ refl (unambiguous l₁ l₂))

@0 nosubstrings : NoSubstrings Length
nosubstrings xs₁++ys₁≡xs₂++ys₂ (short (mkShort l l<128 refl)) (short (mkShort l₁ l<129 refl)) =
  cong [_] (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂)
nosubstrings xs₁++ys₁≡xs₂++ys₂ (short (mkShort l l<128 refl)) (long (mkLong l₁ l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl)) =
  contradiction l<128 (<⇒≯ (subst (λ i → 128 < toℕ i) (sym $ ∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂) l>128))
nosubstrings xs₁++ys₁≡xs₂++ys₂ (long (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl)) (short (mkShort l₁ l<128 refl)) =
  contradiction l<128 (<⇒≯ (subst (λ i → 128 < toℕ i)  (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂) l>128))
nosubstrings xs₁++ys₁≡xs₂++ys₂ (long (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl)) (long (mkLong l₁ l>129 lₕ₁ lₕ≢1 lₜ₁ lₜLen₁ lₕₜMinRep₁ refl)) =
  begin (l ∷ lₕ ∷ lₜ   ≡⟨ cong (_∷ lₕ ∷ lₜ) (‼ l≡) ⟩
        l₁ ∷ lₕ ∷ lₜ   ≡⟨ cong (λ x → l₁ ∷ x ∷ lₜ) (‼ lₕ≡) ⟩
        l₁ ∷ lₕ₁ ∷ lₜ  ≡⟨ cong (λ x → l₁ ∷ lₕ₁ ∷ x) (‼ lₜ≡) ⟩
        l₁ ∷ lₕ₁ ∷ lₜ₁ ∎)
  where
  open ≡-Reasoning

  @0 l≡ : l ≡ l₁
  l≡ = ∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂

  @0 lₕ≡ : lₕ ≡ lₕ₁
  lₕ≡ = ∷-injectiveˡ (∷-injectiveʳ xs₁++ys₁≡xs₂++ys₂)

  @0 lₜ++ys₁≡ : lₜ ++ _ ≡ lₜ₁ ++ _
  lₜ++ys₁≡ = ∷-injectiveʳ (∷-injectiveʳ xs₁++ys₁≡xs₂++ys₂)

  @0 lₜ≡ : lₜ ≡ lₜ₁
  lₜ≡ =
    proj₁ $ Lemmas.length-++-≡ _ _ _ _ lₜ++ys₁≡
              (trans lₜLen (trans (cong (λ x → toℕ x ∸ 129) l≡) (sym lₜLen₁)))

getLength∘toLength-short : (n : Fin 128) → getLength (toLength n) ≡ toℕ n
getLength∘toLength-short n = Fin.toℕ-inject≤ n (toWitness{Q = _ ≤? _} tt)

getLengthRaw>128 : ∀ {lₕ lₜ} → toℕ lₕ > 0 → MinRepLong lₕ lₜ → getLengthRaw (lₕ ∷ lₜ) ≥ 128
getLengthRaw>128 {lₕ} {[]} lₕ>0 mr =
  ≤.begin
    128 ≤.≤⟨ mr ⟩
    toℕ lₕ ≤.≡⟨ sym (*-identityʳ _) ⟩
    toℕ lₕ * 1 ≤.≡⟨ sym (+-identityʳ _) ⟩
    toℕ lₕ * 1 + 0 ≤.∎
  where
  module ≤ = ≤-Reasoning
getLengthRaw>128 {lₕ} {x ∷ lₜ} lₕ>0 tt =
  ≤.begin
    128 ≤.≤⟨ toWitness{Q = 128 ≤? 256} tt ⟩
    256 ≤.≤⟨ m≤m*n 256 (0 < (256 ^ (length lₜ)) ∋ n≢0⇒n>0 (λ ≡0 → contradiction (m^n≡0⇒m≡0 256 (length lₜ) ≡0) λ ())) ⟩
    256 ^ (1 + length lₜ) ≤.≡⟨ sym (*-identityˡ _) ⟩
    1 * 256 ^ (1 + length lₜ) ≤.≤⟨ *-monoˡ-≤ (256 ^ (1 + length lₜ)) lₕ>0 ⟩
    toℕ lₕ * 256 ^ (1 + length lₜ) ≤.≤⟨ m≤m+n _ _ ⟩
    toℕ lₕ * (256 ^ (1 + length lₜ)) + getLengthRaw (x ∷ lₜ) ≤.∎
  where
  module ≤ = ≤-Reasoning

@0 nonmalleable : NonMalleable RawLength
nonmalleable s₁@(short (mkShort l l<128 refl)) s₂@(short (mkShort l₁ l<129 refl)) eq =
  case Fin.toℕ-injective eq ret (const _) of λ where
    refl → case (‼ unambiguous s₁ s₂) ret (const _) of λ where
      refl → refl
nonmalleable (short s₁) (long l₁@(mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRepLong bs≡)) eq =
  contradiction eq
    (<⇒≢ (≤.begin
      1 + toℕ (Short.l s₁) ≤.≤⟨ Short.l<128 s₁ ⟩
      128 ≤.≤⟨ getLengthRaw>128 lₕ≢0 lₕₜMinRepLong ⟩
      getLengthRaw (lₕ ∷ lₜ) ≤.∎))
  where
  module ≤ = ≤-Reasoning
nonmalleable (long (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRepLong bs≡)) (short s₂) eq =
  contradiction eq
    (>⇒≢ (≤.begin
      1 + toℕ (Short.l s₂) ≤.≤⟨ Short.l<128 s₂ ⟩
      128 ≤.≤⟨ getLengthRaw>128 lₕ≢0 lₕₜMinRepLong ⟩
      getLengthRaw (lₕ ∷ lₜ) ≤.∎))
  where
  module ≤ = ≤-Reasoning
nonmalleable{bs₁}{bs₂} len₁@(long (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRepLong refl)) len₂@(long (mkLong l₁ l>129 lₕ₁ lₕ≢1 lₜ₁ lₜLen₁ lₕₜMinRepLong₁ refl)) eq =
  case ‼ bs₁≡bs₂ ret (const _) of λ where
    refl → case (‼ unambiguous len₁ len₂) ret (const _) of λ where
      refl → refl
  where
  module ≤ = ≤-Reasoning
  @0 bs₁≡bs₂ : bs₁ ≡ bs₂
  bs₁≡bs₂ = case <-cmp (length bs₁) (length bs₂) ret (const _) of λ where
    (tri< (s≤s bs₁<bs₂) _ _) →
      contradiction (UInt8.unsigned-leading-0{bs₁ = lₕ ∷ lₜ}{bs₂ = lₕ₁ ∷ lₜ₁} (s≤s z≤n) bs₁<bs₂ eq) (>⇒≢ lₕ≢1)
    (tri≈ _ len≡ _) →
      cong₂ _∷_
        (Fin.toℕ-injective
          (‼ ∸-cancelʳ-≡ l>128 l>129
            (trans (sym lₜLen) (trans (+-cancelˡ-≡ 2 len≡) lₜLen₁))))
        (‼ UInt8.unsigned-injective _ _ (suc-injective len≡) eq)
    (tri> _ _ (s≤s bs₂<bs₁)) →
      contradiction (UInt8.unsigned-leading-0 {bs₁ = lₕ₁ ∷ lₜ₁} {bs₂ = lₕ ∷ lₜ} (s≤s z≤n) bs₂<bs₁ (sym eq)) (>⇒≢ lₕ≢0)
