open import Armor.Arith
open import Armor.Binary
open import Armor.Data.X690-DER.Time.TimeType.TCB
import      Armor.Grammar.Definitions
open import Armor.Prelude

module Armor.Data.X690-DER.Time.TimeType.Properties where

open Armor.Grammar.Definitions              UInt8

fromℕ? : ∀ {size l u} → (n : ℕ) → Dec (TimeType size l u (encodeℕ size n))
fromℕ?{size}{l}{u} n =
  case inRange? l u n' ret (const _) of λ where
    (no ¬p) → no λ where
      (mkTimeType charset (singleton _ refl) bsLen range) →
        contradiction
          (subst₀ (λ x → l ≤ x × x ≤ u)
            (UInt8.asciiNum∘showFixed≗id size n' (Lemmas.m%n<n' n (10 ^ size)))
            range)
          ¬p
    (yes l≤n'≤u) →
      yes
        (mkTimeType
          (fromWitness (proj₂ (proj₂ (showFixed' size n'))))
          (singleton n' (sym (UInt8.asciiNum∘showFixed≗id size n' (Lemmas.m%n<n' n (10 ^ size)))))
          (proj₁ (proj₂ (showFixed' size n')))
          l≤n'≤u)
  where
  n' = n mod10^n size

@0 nosubstrings : ∀ {size l u} → NoSubstrings (TimeType size l u)
nosubstrings xs₁++ys₁≡xs₂++ys₂ (mkTimeType charset time bsLen range) (mkTimeType charset₁ time₁ bsLen₁ range₁) =
  proj₁ (Lemmas.length-++-≡ _ _ _ _ xs₁++ys₁≡xs₂++ys₂ (trans bsLen (sym bsLen₁)))

@0 unambiguous : ∀ {size l u} → Unambiguous (TimeType size l u)
unambiguous {._} {l} {u} {xs} (mkTimeType charset time refl range) (mkTimeType charset₁ time₁ refl range₁) =
  case (‼ T-unique charset charset₁) ret (const _) of λ where
    refl → case (‼ uniqueSingleton time time₁) ret (const _) of λ where
      refl → case (‼ inRange-unique{A = ℕ}{x = time} range range₁) ret (const _) of λ where
        refl → refl

@0 nonmalleable : ∀ {size l u} → NonMalleable (RawTimeType size l u)
nonmalleable{bs₁ = bs₁}{bs₂} time₁@(mkTimeType charset (singleton t₁ t₁≡) bsLen range) time₂@(mkTimeType charset₁ (singleton t₂ t₂≡) bsLen₁ range₁) eq =
  case
    (‼ UInt8.asciiNum-injective bs₁ bs₂ (toWitness charset) (toWitness charset₁)
         (trans bsLen (sym bsLen₁)) (trans (sym t₁≡) (trans eq t₂≡)))
  ret (const _) of λ where
    refl → case (‼ unambiguous time₁ time₂) ret (const _) of λ where
      refl → refl

instance
  eq : ∀ {size l u} → Eq (Exists─ (List UInt8) (TimeType size l u))
  Eq._≟_ eq (─ _ , t₁) (─ _ , t₂) =
    case Raw.to (RawTimeType _ _ _) t₁ ≟ Raw.to (RawTimeType _ _ _) t₂ ret (const _) of λ where
      (no ¬p) → no (λ where refl → contradiction refl ¬p)
      (yes p) → yes (‼ nonmalleable t₁ t₂ p)

  eq≋ : ∀ {size l u} → Eq≋ (TimeType size l u)
  eq≋ = Eq⇒Eq≋ eq
