open import Armor.Prelude

open import Armor.Binary
import      Armor.Grammar.Definitions
open import Armor.Grammar.Parallel
open import Armor.Grammar.Parser
open import Armor.Data.X690-DER.Length.TCB
open import Armor.Data.X690-DER.Length.Properties

open import Data.Nat.Properties
  hiding (_≟_)
open import Data.List.Properties

module Armor.Data.X690-DER.Length.Parser where

open Armor.Grammar.Definitions UInt8

module parseShortLen where
  here' = "parseShortLen"

  parseShortLen : Parser UInt8 (Logging ∘ Dec) Short
  runParser parseShortLen [] = do
    tell $ here' String.++ ": underflow reading length"
    return ∘ no $ λ where
      (success .([ l ]) read read≡ (mkShort l l<128 refl) suffix ())
  runParser parseShortLen (l ∷ xs)
    with toℕ l <? 128
  ... | no  l≮128 =
    return ∘ no $ λ where
      (success .([ l ]) read read≡ (mkShort l l<128 refl) suffix refl) →
        contradiction l<128 l≮128
  ... | yes l<128 =
    return (yes (success [ l ] 1 refl (mkShort l l<128 refl) xs refl))

open parseShortLen public using (parseShortLen)

module parseLongLen where
  here' = "parseLongLen"

  open ≡-Reasoning

  parseLongLen : Parser UInt8 (Logging ∘ Dec) Long
  runParser parseLongLen [] = do
    tell $ here' String.++ ": underflow reading length"
    return ∘ no $ λ where
      (success .(l ∷ lₕ ∷ lₜ) read read≡ (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl) suffix ())
  runParser parseLongLen (l ∷ []) = do
    tell $ here' String.++ ": underflow reading (long) length"
    return ∘ no $ λ where
      (success .(l ∷ lₕ ∷ lₜ) read read≡ (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl) suffix ())
  runParser parseLongLen (l ∷ lₕ ∷ xs)
    with 128 <? toℕ l
  ... | no  l≯128 = do
    tell $ here' String.++ ": leading byte value to small for long length"
    return ∘ no $ λ where
      (success .(l ∷ lₕ ∷ lₜ) read read≡ (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl) suffix refl) →
        contradiction l>128 l≯128
  ... | yes l>128
    with toℕ lₕ >? 0
  ... | no  lₕ≡0 = do
    tell $ here' String.++ ": first byte of length sequence must not be zero"
    return ∘ no $ λ where
      (success .(l ∷ lₕ ∷ lₜ) read read≡ (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl) suffix refl) →
        contradiction lₕ≢0 lₕ≡0
  ... | yes lₕ≢0 = do
    yes (success pre₀ r₀ r₀≡ (mk×ₚ (singleton lₜ refl) (─ lₜLen)) suf₀ refl)
      ← runParser (parseN _ (toℕ l - 129) (return (Level.lift tt))) xs
      where no ¬parse → do
        tell $ here' String.++ ": underflow reading length sequence: " String.++ (String.showNat $ toℕ l - 128)
        return ∘ no $ λ where
          (success .(l ∷ lₕ ∷ lₜ) read read≡ (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl) suffix refl) →
            contradiction (success lₜ (length lₜ) refl (mk×ₚ (singleton lₜ refl) (─ lₜLen)) suffix refl)
              ¬parse
    case lₜ ≟ [] of λ where
      (no  lₜ≢[]) →
        return (yes
          (success (l ∷ lₕ ∷ lₜ) _ (cong (2 +_) r₀≡ )
            (mkLongₛ l lₕ lₜ{fromWitness l>128}{fromWitness lₕ≢0}{fromWitness lₜLen}{fromWitness (inj₁ lₜ≢[])})
            suf₀ refl))
      (yes lₜ≡[]) →
        case toℕ lₕ ≥? 128 of λ where
          (no  lₕ≱128) → do
            tell $ here' String.++ ": long length used where short length would suffice"
            return ∘ no $ λ where
              (success prefix read read≡ (mkLong l' l'>128 lₕ' lₕ'≢0 lₜ' lₜ'Len lₕₜMinRep' refl) suffix ps≡) → ‼
                let @0 l≡ : l' ≡ l
                    l≡ = ∷-injectiveˡ ps≡

                    @0 lₕ≡ : lₕ' ≡ lₕ
                    lₕ≡ = ∷-injectiveˡ (∷-injectiveʳ ps≡)

                    @0 lₜ≡ : lₜ' ≡ lₜ × suffix ≡ suf₀
                    lₜ≡ = Lemmas.length-++-≡ _ _ _ _ (∷-injectiveʳ (∷-injectiveʳ ps≡)) $ begin
                      length lₜ'   ≡⟨ lₜ'Len ⟩
                      toℕ l' - 129 ≡⟨ cong (λ i → toℕ i - 129) l≡ ⟩
                      toℕ l - 129  ≡⟨ sym lₜLen ⟩
                      length lₜ    ∎
                in
                elimMinRepLong lₕ' lₜ' (λ _ _ → ⊥)
                  (λ lₜ'≡[] lₕ'≥128 → contradiction lₕ'≥128 (subst (λ i → ¬ 128 ≤ toℕ i) (sym lₕ≡) lₕ≱128))
                  (λ lₜ'≢[] → contradiction (trans (proj₁ lₜ≡) lₜ≡[]) lₜ'≢[])
                  lₕₜMinRep'
          (yes lₕ≥128) →
            return (yes
              (success _ _ refl
                (mkLongₛ l lₕ lₜ{fromWitness l>128}{fromWitness lₕ≢0}{fromWitness lₜLen}{fromWitness (inj₂ lₕ≥128)}) suf₀ refl))

open parseLongLen public using (parseLongLen)

module parseLen where
  here' = "parseLen"

  parseLen : Parser UInt8 (Logging ∘ Dec) Length
  runParser parseLen xs = do
    no ¬short ← runParser parseShortLen xs
      where yes sho → return (yes (mapSuccess _ (λ {xs'} → short {xs'}) sho))
    no ¬long  ← runParser parseLongLen xs
      where yes lo → return (yes (mapSuccess _ (λ {xs'} → long {xs'}) lo))
    return ∘ no $ λ where
      (success prefix read read≡ (short sho) suffix ps≡) →
        contradiction (success prefix read read≡ sho suffix ps≡) ¬short
      (success prefix read read≡ (long lo) suffix ps≡) →
        contradiction (success _ _ read≡ lo _ ps≡) ¬long

open parseLen public using (parseLen)
