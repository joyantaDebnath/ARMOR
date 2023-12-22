open import Armor.Binary
open import Armor.Data.X690-DER.BitString.Properties
open import Armor.Data.X690-DER.BitString.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parser
import      Armor.Grammar.Parallel
open import Armor.Prelude
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X690-DER.BitString.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Parallel    UInt8

module parseBitstring where
  open ≡-Reasoning

  here' = "parseBitstring"

  parseBitstringValue : ∀ n → Parser (Logging ∘ Dec) (ExactLength BitStringValue n)
  runParser (parseBitstringValue n) xs = do
    yes (success .(bₕ ∷ bₜ) r₀ r₀≡ (mk×ₚ (singleton (bₕ ∷ bₜ) refl) (─ bsLen)) suf₀ ps≡₀) ←
      runParser (parseN n (tell $ here' String.++ ": underflow")) xs
      where
        (yes (success .[] .0 refl (mk×ₚ (singleton [] refl) (─ refl)) .xs refl)) →
          return ∘ no $ λ where
            (success .(bₕ ∷ bₜ) read read≡ (mk×ₚ (mkBitStringValue bₕ bₜ bₕ<8 bits unusedBits refl) ()) suffix ps≡)
        (no ¬parse) →
          return ∘ no $ λ where
            (success .(bₕ ∷ bₜ) read read≡ (mk×ₚ (mkBitStringValue bₕ bₜ bₕ<8 bits unusedBits refl) sndₚ₁) suffix ps≡) →
              contradiction
                (success (bₕ ∷ bₜ) _ read≡ (mk×ₚ self sndₚ₁) suffix ps≡)
                ¬parse
    case toℕ bₕ <? 8 of λ where
      (no bₕ≮8) → do
        tell $ here' String.++ ": unused bits field too large"
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ (mkBitStringValue bₕ bₜ bₕ<8 bits unusedBits refl) sndₚ₁) suffix ps≡) →
            contradiction
              (≤-trans (Lemmas.≡⇒≤ (cong (suc ∘ toℕ) (∷-injectiveˡ (trans₀ ps≡₀ (sym ps≡))))) bₕ<8)
              bₕ≮8
      (yes bₕ<8) →
        case unusedBits? bₕ bₜ of λ where
          (no ¬validunused) → do
            tell $ here' String.++ ": bad unused bits"
            return ∘ no $ λ where
              (success prefix read read≡ (mk×ₚ (mkBitStringValue bₕ' bₜ' _ _ unusedBits refl) (─ sndₚ₁)) suffix ps≡) →
                contradiction
                  (subst₂ UnusedBits{x = bₕ'}{u = bₜ'}{bₜ}
                    (∷-injectiveˡ (trans₀ ps≡ (sym ps≡₀)))
                    (∷-injectiveʳ (Parallel.ExactLength.nosubstrings _ (trans₀ ps≡ (sym ps≡₀))
                                    (mk×ₚ{A = Singleton} self (─ sndₚ₁))
                                    (mk×ₚ self (─ bsLen))))
                    unusedBits)
                  ¬validunused
          (yes validunused) →
            return (yes
              (success (bₕ ∷ bₜ) _ r₀≡ (mk×ₚ (mkBitStringValue bₕ bₜ bₕ<8 self validunused refl) (─ bsLen)) suf₀ ps≡₀))

  parseBitstring : Parser (Logging ∘ Dec) BitString
  parseBitstring =
    parseTLV Tag.BitString here' BitStringValue parseBitstringValue

open parseBitstring public using (parseBitstringValue ; parseBitstring)

-- private
--   module Test where

--     Bitstring₁ : List Dig
--     Bitstring₁ = Tag.BitString ∷ # 2 ∷ # 5 ∷ [ # 160 ]

--     Bitstring₂ : List Dig
--     Bitstring₂ = Tag.BitString ∷ # 2 ∷ # 0 ∷ [ # 160 ]

--     Bitstring₃ : List Dig
--     Bitstring₃ = Tag.BitString ∷ # 2 ∷ # 7 ∷ [ # 160 ]

--     Bitstring₄ : List Dig
--     Bitstring₄ = Tag.BitString ∷ # 2 ∷ # 8 ∷ [ # 160 ]

--     Bitstring₅ : List Dig
--     Bitstring₅ = Tag.BitString ∷ # 3 ∷ # 8 ∷ # 255 ∷ [ # 160 ]

--     Bitstring₆ : List Dig
--     Bitstring₆ = Tag.BitString ∷ # 1 ∷ [ # 0 ]

--     Bitstring₇ : List Dig
--     Bitstring₇ = Tag.BitString ∷ # 1 ∷ [ # 3 ]

--     test₁ : BitString Bitstring₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseBitstring Bitstring₁)} tt)

--     test₂ : BitString Bitstring₂
--     test₂ = Success.value (toWitness {Q = Logging.val (runParser parseBitstring Bitstring₂)} tt)

--     test₃ : ¬ Success _ BitString Bitstring₃
--     test₃ = toWitnessFalse {Q = Logging.val (runParser parseBitstring Bitstring₃)} tt

--     test₄ : ¬ Success _ BitString Bitstring₄
--     test₄ = toWitnessFalse {Q = Logging.val (runParser parseBitstring Bitstring₄)} tt

--     test₅ : ¬ Success _ BitString Bitstring₅
--     test₅ = toWitnessFalse {Q = Logging.val (runParser parseBitstring Bitstring₅)} tt

--     test₆ : BitString Bitstring₆
--     test₆ = Success.value (toWitness {Q = Logging.val (runParser parseBitstring Bitstring₆)} tt)

--     test₇ : ¬ Success _ BitString Bitstring₇
--     test₇ = toWitnessFalse {Q = Logging.val (runParser parseBitstring Bitstring₇)} tt

