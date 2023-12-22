open import Armor.Binary
  renaming (module Base64 to B64)
open import Armor.Data.Base64
open import Armor.Data.PEM.RFC5234.TCB
  hiding (module EOL)
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Sum
open import Armor.Prelude
import      Data.List.Relation.Unary.Any.Properties as Any

module Armor.Data.PEM.RFC5234.Properties where

open Armor.Grammar.Definitions Char
open Armor.Grammar.Parallel    Char
open Armor.Grammar.Sum         Char

module EOL where
  Rep =  Sum (λ x → Erased (x ≡ '\r' ∷ [ '\n' ]))
        (Sum (λ x → Erased (x ≡ [ '\r' ]))
             (λ x → Erased (x ≡ [ '\n' ])))

  @0 char∈ : ∀ {@0 b bs} → b ∈ bs → EOL bs → b ≡ '\r' ⊎ b ≡ '\n'
  char∈ (here refl) crlf = inj₁ refl
  char∈ (there (here refl)) crlf = inj₂ refl
  char∈ (here refl) cr = inj₁ refl
  char∈ (here refl) lf = inj₂ refl

  char₁ : ∀ {@0 b bs} → EOL (b ∷ bs) → b ≡ '\r' ⊎ b ≡ '\n'
  char₁ crlf = inj₁ refl
  char₁ cr = inj₁ refl
  char₁ lf = inj₂ refl

  equiv : Equivalent Rep EOL
  proj₁ equiv (Sum.inj₁ (─ refl)) = crlf
  proj₁ equiv (Sum.inj₂ (Sum.inj₁ (─ refl))) = cr
  proj₁ equiv (Sum.inj₂ (Sum.inj₂ (─ refl))) = lf
  proj₂ equiv crlf = Sum.inj₁ (─ refl)
  proj₂ equiv cr = Sum.inj₂ (Sum.inj₁ (─ refl))
  proj₂ equiv lf = Sum.inj₂ (Sum.inj₂ (─ refl))

  @0 eolLen : ∀ {@0 bs} → EOL bs → InRange 1 2 (length bs)
  eolLen crlf = toWitness{Q = inRange? 1 2 2} tt
  eolLen cr = toWitness{Q = inRange? 1 2 1} tt
  eolLen lf = toWitness{Q = inRange? 1 2 1} tt

  noOverlap : NoOverlap Base64Str EOL
  noOverlap ws [] ys₁ xs₂ ys₂ xs₁++ys₁≡xs₂++ys₂ str₁ str₂ =
    inj₁ refl
  noOverlap ws xs₁@(x₁' ∷ xs₁') ys₁ xs₂ ys₂ xs₁++ys₁≡xs₂++ys₂ str₁ str₂ =
    inj₂ absurd
    where
    xs₂≡ : EOL xs₂ → Σ[ p ∈ (Char × List Char) ] uncurry _∷_ p ≡ xs₂
    xs₂≡ crlf = -, refl
    xs₂≡ cr = -, refl
    xs₂≡ lf = -, refl
  
    module _ (e : EOL xs₂) where

      x₂' : Char
      x₂' = proj₁ (proj₁ (xs₂≡ e))

      xs₂' : List Char
      xs₂' = proj₂ (proj₁ (xs₂≡ e))

      e' : EOL (x₂' ∷ xs₂')
      e' = subst₀! EOL (sym ∘ proj₂ ∘ xs₂≡ $ e) e

      e“ : EOL (x₁' ∷ xs₂')
      e“ = subst₀ (λ x → EOL (x ∷ xs₂'))
             (∷-injectiveˡ
               (trans
                 (cong (_++ ys₂) ((proj₂ ∘ xs₂≡ $ e)))
                 (sym xs₁++ys₁≡xs₂++ys₂)))
             e'

      x₁'∈ : x₁' ∈ B64.charset ⊎ x₁' ≡ '='
      x₁'∈ = Base64.Str.char∈ (Any.++⁺ʳ ws (here refl)) str₁

      absurd : ⊥
      absurd =
        contradiction{P = x₁' ≡ '\r' ⊎ x₁' ≡ '\n'}
          (char₁ e“)
          λ where
            (inj₁ refl) →
              contradiction₂ x₁'∈ (toWitnessFalse{Q = _ ∈? _} tt) λ ()
            (inj₂ refl) → contradiction₂ x₁'∈ (toWitnessFalse{Q = _ ∈? _} tt) (λ ())

  noOverlap' : NoOverlap EOL (Length≥ Base64Str 1)
  noOverlap' .('\r' ∷ [ '\n' ]) .[] ys₁ xs₂ ys₂ x crlf crlf = inj₁ refl
  noOverlap' .([ '\r' ]) .([ '\n' ]) ys₁ xs₂ ys₂ ++≡ crlf cr =
    inj₂ λ where
      x₁@(mk×ₚ x₁' x₁'Len) → contradiction₂ (Base64.Str.char∈ ('\n' ∈ xs₂ ∋ n∈ x₁ x₁'Len) x₁')
        (toWitnessFalse{Q = _ ∈? _} tt)
        (λ ())
    where
    module _ (x₁ : Length≥ Base64Str 1 xs₂) (x₁Len : Erased (length xs₂ > 0)) where
      n∈ : '\n' ∈ xs₂
      n∈ = case singleton xs₂ refl ret (const _) of λ where
        (singleton [] refl) → contradiction (¡ x₁Len) (λ ())
        (singleton (x ∷ x₁) refl) → here (∷-injectiveˡ ++≡)
  noOverlap' .([ '\r' ]) .[] ys₁ xs₂ ys₂ x cr cr = inj₁ refl
  noOverlap' .([ '\n' ]) .[] ys₁ xs₂ ys₂ x lf lf = inj₁ refl

  @0 unambiguous : Unambiguous EOL
  unambiguous crlf crlf = refl
  unambiguous cr cr = refl
  unambiguous lf lf = refl
