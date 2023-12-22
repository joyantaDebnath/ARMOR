open import Armor.Prelude
import Armor.Grammar.Definitions.NonMalleable

module Armor.Grammar.Option.TCB (Σ : Set) where

open Armor.Grammar.Definitions.NonMalleable Σ

data Option (A : @0 List Σ → Set) : (@0 _ : List Σ) → Set where
 none : Option A []
 some : ∀ {@0 xs} → A xs → Option A xs

elimOption : ∀ {@0 A} {X : List Σ → Set} → X [] → (∀ {@0 xs} → A xs → X xs) → ∀ {@0 xs} → Option A xs → X xs
elimOption n s none = n
elimOption n s (some x) = s x

isNone : ∀ {@0 A xs} →  Option A xs → Bool
isNone none = true
isNone (some _) = false

isSome : ∀ {@0 A xs} → Option A xs → Bool
isSome x = not (isNone x)

mapOption : ∀ {@0 A B} → (∀ {@0 xs} → A xs → B xs) → ∀ {@0 xs} → Option A xs → Option B xs
mapOption f none = none
mapOption f (some x) = some (f x)

mapOptionK : ∀ {@0 A B xs} → (A xs → B xs) → Option A xs → Option B xs
mapOptionK f none = none
mapOptionK f (some x) = some (f x)

RawOption : ∀ {A} → Raw A → Raw (Option A)
Raw.D (RawOption x) = Maybe (Raw.D x)
Raw.to (RawOption x) none = nothing
Raw.to (RawOption x) (some x₁) = just (Raw.to x x₁)
