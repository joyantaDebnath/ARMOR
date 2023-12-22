import      Armor.Grammar.Definitions
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.Parallel.TCB
open import Armor.Prelude
  hiding (head ; tail)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Grammar.IList.TCB (Σ : Set) where

open Armor.Grammar.Definitions  Σ
open Armor.Grammar.Parallel.TCB Σ

data IList (A : @0 List Σ → Set) : @0 List Σ → Set

record IListCons (A : @0 List Σ → Set) (@0 bs : List Σ) : Set where
  inductive
  constructor mkIListCons
  field
    @0 {bs₁ bs₂} : List Σ
    head : A bs₁
    tail : IList A bs₂
    @0 bs≡ : bs ≡ bs₁ ++ bs₂

data IList A where
  nil : IList A []
  cons : ∀ {@0 xs} → IListCons A xs → IList A xs

pattern consIList{bs₁}{bs₂} h t bs≡ = cons (mkIListCons{bs₁}{bs₂} h t bs≡)

mapIList : ∀ {A B} → (∀ {@0 bs} → A bs → B bs) → ∀ {@0 bs} → IList A bs → IList B bs
mapIList f nil = nil
mapIList f (consIList{bs₁}{bs₂} h t refl) = consIList (f h) (mapIList (λ {bs'} → f{bs'}) t) refl

toList : ∀ {@0 A : @0 List Σ → Set} {@0 bs} → IList A bs → List (Exists─ (List Σ) A)
toList nil = []
toList (consIList h₁ t₁ bs≡₁) = (─ _ , h₁) ∷ toList t₁

appendIList : ∀ {@0 A xs₁ xs₂} → IList A xs₁ → IList A xs₂ → IList A (xs₁ ++ xs₂)
appendIList nil x₁ = x₁
appendIList (cons (mkIListCons head tail refl)) x₁
  with appendIList tail x₁
... | y = cons (mkIListCons head y (solve (++-monoid Σ)))

reverseIList : ∀ {@0 A xs} → IList A xs → Exists─ _ (IList A)
reverseIList x = helper x nil
  where
  helper : ∀ {@0 A xs₁ xs₂} → IList A xs₁ → IList A xs₂ → Exists─ _ (IList A)
  helper nil x₁ = _ , x₁
  helper (cons (mkIListCons head tail bs≡)) x₁ = helper tail (appendIList (cons (mkIListCons head nil refl)) x₁)

lengthIList : ∀ {@0 A xs} → IList A xs → ℕ
lengthIList nil = 0
lengthIList (cons (mkIListCons h t bs≡)) = 1 + lengthIList t

IListLowerBounded : (A : @0 List Σ → Set) → @0 ℕ → @0 List Σ → Set
IListLowerBounded A n = Σₚ (IList A) (λ s xs → Erased (lengthIList xs ≥ n))

IListNonEmpty : (A : @0 List Σ → Set) → @0 List Σ → Set
IListNonEmpty A = IListLowerBounded A 1

RawIList : {A : @0 List Σ → Set} → Raw A → Raw (IList A)
Raw.D (RawIList R) = List (Raw.D R)
Raw.to (RawIList R) = map (λ where (─ xs , e) → Raw.to R{xs = xs} e) ∘ toList
