open import Armor.Binary
open import Armor.Data.X690-DER.Time.TimeType.Properties
open import Armor.Data.X690-DER.Time.TimeType.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X690-DER.Time.TimeType.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

private
  here' = "X690-DER: Time: TimeType"

parse : ∀ size l u → Parser (Logging ∘ Dec) (TimeType size l u)
runParser (parse size l u) xs = do
  (yes (success ._ r₁ r₁≡ (mk×ₚ (singleton v₁ refl) (─ v₁Len)) suf₁ ps≡₁))
    ← runParser (parseN size (tell $ here' String.++ ": underflow")) xs
    where no ¬p → do
      return ∘ no $ λ where
        (success prefix read read≡ (mkTimeType charset time bsLen range) suffix ps≡) →
          contradiction (success prefix _ read≡ (mk×ₚ self (─ bsLen)) suffix ps≡) ¬p
  case All.all? (inRange? '0' '9') v₁ ret (const _) of λ where
    (no ¬p) → do
      tell $ here' String.++ ": bad character range: " String.++ show (map Fin.toℕ v₁)
      return ∘ no $ λ where
        (success prefix read read≡ (mkTimeType charset time bsLen range) suffix ps≡) →
          contradiction
            (subst (All (InRange '0' '9'))
              (proj₁ (Lemmas.length-++-≡ _ suffix v₁ suf₁ (trans ps≡ (sym ps≡₁)) (trans bsLen (sym v₁Len))))
              (toWitness charset))
            ¬p
    (yes ir) → do
      let t = asciiNum v₁
      case inRange? l u t ret (const _) of λ where
        (no ¬p) → do
          tell $ here' String.++ ": bad time range: " String.++ show t
          return ∘ no $ λ where
            (success prefix read read≡ (mkTimeType charset time bsLen range) suffix ps≡) →
              let
                prefix≡v₁ : Erased (prefix ≡ v₁)
                prefix≡v₁ = ─ proj₁ (Lemmas.length-++-≡ prefix suffix v₁ suf₁ (trans ps≡ (sym ps≡₁)) (trans bsLen (sym v₁Len)))
              in
              contradiction
                (subst (λ x → l ≤ x × x ≤ u) (trans (Singleton.x≡ time) (cong asciiNum (¡ prefix≡v₁))) range)
                ¬p
        (yes p) → return (yes
          (success v₁ _ r₁≡ (mkTimeType (fromWitness ir ) self v₁Len p) suf₁ ps≡₁))
