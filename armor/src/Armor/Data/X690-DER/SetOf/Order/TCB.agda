open import Armor.Binary
open import Armor.Data.X690-DER.SequenceOf.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Parallel.TCB
open import Armor.Prelude
open import Relation.Binary.Bundles
open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.Structures
import      Data.List.Sort
import      Data.Nat.Properties as Nat

module Armor.Data.X690-DER.SetOf.Order.TCB where

open Armor.Grammar.Parallel.TCB UInt8

infix 4 _≈_ _≈?_ _≲_ _≲?_

_≈_ : Rel (List UInt8) Level.0ℓ
[] ≈ y = All (_≡ (# 0)) y
x@(_ ∷ _) ≈ [] = All (_≡ (# 0)) x
(x₁ ∷ x) ≈ (y₁ ∷ y) = x₁ ≡ y₁ × x ≈ y

≈-reflexive : Reflexive _≈_
≈-reflexive {[]} = []
≈-reflexive {x ∷ x₁} = refl , ≈-reflexive

≈-symmetric : Symmetric _≈_
≈-symmetric {[]} {[]} x≈y = []
≈-symmetric {[]} {x ∷ y} x≈y = x≈y
≈-symmetric {x ∷ x₁} {[]} x≈y = x≈y
≈-symmetric {x ∷ x₁} {x₂ ∷ y} x≈y = (sym (proj₁ x≈y)) , ≈-symmetric (proj₂ x≈y)

all0∧≈⇒all0 : ∀ {x y} → All (_≡ # 0) x → x ≈ y → All (_≡ # 0) y
all0∧≈⇒all0 {.[]} {y} [] x≈y = x≈y
all0∧≈⇒all0 {.(_ ∷ _)} {[]} (px ∷ allx) x≈y = []
all0∧≈⇒all0 {.(_ ∷ _)} {x ∷ y} (px ∷ allx) (refl , x≈y) = px ∷ all0∧≈⇒all0 allx x≈y

all0∧all0⇒≈ : ∀ {x y} → All (_≡ # 0) x → All (_≡ # 0) y → x ≈ y
all0∧all0⇒≈ {.[]} {y} [] ally = ally
all0∧all0⇒≈ {.(_ ∷ _)} {.[]} (px ∷ allx) [] = px ∷ allx
all0∧all0⇒≈ {.(_ ∷ _)} {.(_ ∷ _)} (refl ∷ allx) (refl ∷ ally) = refl , (all0∧all0⇒≈ allx ally)

≈-transitive : Transitive _≈_
≈-transitive {[]} {y} {z} x≈y y≈z = all0∧≈⇒all0 x≈y y≈z
≈-transitive {x ∷ x₁} {[]} {z} x≈y y≈z = all0∧all0⇒≈ x≈y y≈z
≈-transitive {x ∷ x₁} {.x ∷ y} {[]} (refl , x≈y) (px ∷ y≈z) = px ∷ (all0∧≈⇒all0 {x = y} {y = x₁} y≈z (≈-symmetric x≈y))
≈-transitive {x ∷ x₁} {.x ∷ y} {x₂ ∷ z} (refl , x≈y) (refl , y≈z) = refl , (≈-transitive x≈y y≈z)

_≈?_ : Decidable₂ _≈_
[] ≈? y = All.all? (_≟ (# 0)) y
x@(_ ∷ _) ≈? [] = All.all? (_≟ (# 0)) x
(x₁ ∷ x) ≈? (y₁ ∷ y) = (x₁ ≟ y₁) ×-dec (x ≈? y)

_≲_ : Rel (List UInt8) Level.0ℓ
[] ≲ y = ⊤
x@(_ ∷ _) ≲ [] = All ((_≡ (# 0))) x
(x₁ ∷ x) ≲ (y₁ ∷ y) = x₁ Fin.< y₁ ⊎ (x₁ ≡ y₁ × x ≲ y)

all0⇒≲ : ∀ {x y} → All (_≡ # 0) x → x ≲ y
all0⇒≲ {.[]} [] = tt
all0⇒≲ {.(_ ∷ _)} {[]} (px ∷ allx) = px ∷ allx
all0⇒≲ {.(# 0 ∷ _)} {Fin.zero ∷ y} (refl ∷ allx) = inj₂ (refl , (all0⇒≲ allx))
all0⇒≲ {.(# 0 ∷ _)} {Fin.suc x ∷ y} (refl ∷ allx) = inj₁ (s≤s z≤n)

all0∧≲⇒all0 : ∀ {x y} → All (_≡ # 0) x → y ≲ x → All (_≡ # 0) y
all0∧≲⇒all0 {x} {[]} allx x≲y = []
all0∧≲⇒all0 {.[]} {y₁ ∷ y} [] x≲y = x≲y
all0∧≲⇒all0 {.(# 0 ∷ _)} {y₁ ∷ y} (refl ∷ allx) (inj₂ (refl , y≲x)) = refl ∷ (all0∧≲⇒all0 allx y≲x)

≲-reflexive-≈ : ∀ {x y} → x ≈ y → x ≲ y
≲-reflexive-≈ {[]} {y} x≈y = tt
≲-reflexive-≈ {x ∷ x₁} {[]} x≈y = x≈y
≲-reflexive-≈ {x ∷ x₁} {x₂ ∷ y} (refl , x≈y) = inj₂ (refl , (≲-reflexive-≈ x≈y))

≲-transitive : Transitive _≲_
≲-transitive {[]} {y} {z} x≲y y≲z = tt
≲-transitive {x ∷ x₁} {[]} {z} x≲y y≲z = all0⇒≲ x≲y
≲-transitive {x₁ ∷ x} {.(# 0) ∷ y} {[]} (inj₂ (refl , x≲y)) (refl ∷ y≲z) = refl ∷ (all0∧≲⇒all0 y≲z x≲y)
≲-transitive {x₁ ∷ x} {y₁ ∷ y} {z₁ ∷ z} (inj₁ x₁<y₁) (inj₁ y₁<z₁) = inj₁ (Nat.<-trans x₁<y₁ y₁<z₁)
≲-transitive {x₁ ∷ x} {y₁ ∷ y} {z₁ ∷ z} (inj₁ x₁<y₁) (inj₂ (refl , y≲z)) = inj₁ x₁<y₁
≲-transitive {x₁ ∷ x} {y₁ ∷ y} {z₁ ∷ z} (inj₂ (refl , x≲y)) (inj₁ y₁<z₁) = inj₁ y₁<z₁
≲-transitive {x₁ ∷ x} {y₁ ∷ y} {z₁ ∷ z} (inj₂ (refl , x≲y)) (inj₂ (refl , y≲z)) = inj₂ (refl , ≲-transitive x≲y y≲z)

≲-antisym-≈ : Antisymmetric _≈_ _≲_
≲-antisym-≈ {[]} {y} x≲y y≲x = all0∧≲⇒all0{x = []} [] y≲x
≲-antisym-≈ {x ∷ x₁} {[]} x≲y y≲x = x≲y
≲-antisym-≈ {x₁ ∷ x} {y₁ ∷ y} (inj₁ x₁<y₁) (inj₁ y₁<x₁) = contradiction x₁<y₁ (Nat.<⇒≯ y₁<x₁)
≲-antisym-≈ {x₁ ∷ x} {y₁ ∷ y} (inj₁ x₁<y₁) (inj₂ (refl , _)) = contradiction x₁<y₁ (Nat.n≮n (toℕ x₁))
≲-antisym-≈ {x₁ ∷ x} {y₁ ∷ y} (inj₂ (refl , x≲y)) (inj₁ y₁<x₁) = contradiction y₁<x₁ (Nat.n≮n (toℕ x₁))
≲-antisym-≈ {x₁ ∷ x} {y₁ ∷ y} (inj₂ (refl , x≲y)) (inj₂ (refl , y≲x)) = refl , (≲-antisym-≈ x≲y y≲x)

_≲?_ : Decidable₂ _≲_
[] ≲? y = yes tt
x@(_ ∷ _) ≲? [] = All.all? (_≟ (# 0)) x
x₁ ∷ x ≲? y₁ ∷ y =
  case Nat.<-cmp (toℕ x₁) (toℕ y₁) of λ where
    (tri< x₁<y₁ _ _) → yes (inj₁ x₁<y₁)
    (tri≈ _ x₁≡y₁ _) →
      case x ≲? y of λ where
        (no ¬p) → no (λ { (inj₁ x) → contradiction x₁≡y₁ (Nat.<⇒≢ x) ; (inj₂ (refl , x≲y)) → contradiction x≲y ¬p })
        (yes p) → yes (inj₂ ((Fin.toℕ-injective x₁≡y₁) , p))
    (tri> ¬x₁<y₁ ¬x₁≡y₁ x₁>y₁) → no λ { (inj₁ x) → contradiction x ¬x₁<y₁ ; (inj₂ (refl , x≲y)) → contradiction refl ¬x₁≡y₁}

bytesIsEquivalence : IsEquivalence _≈_
IsEquivalence.refl bytesIsEquivalence = ≈-reflexive
IsEquivalence.sym bytesIsEquivalence = ≈-symmetric
IsEquivalence.trans bytesIsEquivalence = ≈-transitive

bytesIsPreorder : IsPreorder _≈_ _≲_
IsPreorder.isEquivalence bytesIsPreorder = bytesIsEquivalence
IsPreorder.reflexive bytesIsPreorder = ≲-reflexive-≈
IsPreorder.trans bytesIsPreorder = ≲-transitive

bytesIsPartialOrder : IsPartialOrder _≈_ _≲_
IsPartialOrder.isPreorder bytesIsPartialOrder = bytesIsPreorder
IsPartialOrder.antisym bytesIsPartialOrder = ≲-antisym-≈

bytesTotal : Total _≲_
bytesTotal [] y = inj₁ tt
bytesTotal (x ∷ x₁) [] = inj₂ tt
bytesTotal (x₁ ∷ x) (y₁ ∷ y) =
  case Nat.<-cmp (toℕ x₁) (toℕ y₁) of λ where
    (tri< x₁<y₁ ¬x₁≡y₁ ¬x₁>y₁) → inj₁ (inj₁ x₁<y₁)
    (tri≈ ¬x₁<y₁ x₁≡y₁ ¬x₁>y₁) →
      case bytesTotal x y of λ where
        (inj₁ x≲y) → inj₁ (inj₂ ((Fin.toℕ-injective x₁≡y₁) , x≲y))
        (inj₂ y≲x) → inj₂ (inj₂ ((Fin.toℕ-injective (sym x₁≡y₁)) , y≲x))
    (tri> ¬x₁<y₁ ¬x₁≡y₁ x₁>y₁) → inj₂ (inj₁ x₁>y₁)

bytesIsTotalOrder : IsTotalOrder _≈_ _≲_
IsTotalOrder.isPartialOrder bytesIsTotalOrder = bytesIsPartialOrder
IsTotalOrder.total bytesIsTotalOrder = bytesTotal

bytesTotalOrder : TotalOrder Level.0ℓ Level.0ℓ Level.0ℓ
TotalOrder.Carrier bytesTotalOrder = List UInt8
TotalOrder._≈_ bytesTotalOrder = _≈_
TotalOrder._≤_ bytesTotalOrder = _≲_
TotalOrder.isTotalOrder bytesTotalOrder = bytesIsTotalOrder

bytesIsDecTotalOrder : IsDecTotalOrder _≈_ _≲_
IsDecTotalOrder.isTotalOrder bytesIsDecTotalOrder = bytesIsTotalOrder
IsDecTotalOrder._≟_ bytesIsDecTotalOrder = _≈?_
IsDecTotalOrder._≤?_ bytesIsDecTotalOrder = _≲?_

bytesDecTotalOrder : DecTotalOrder Level.0ℓ Level.0ℓ Level.0ℓ
DecTotalOrder.Carrier bytesDecTotalOrder = List UInt8
DecTotalOrder._≈_ bytesDecTotalOrder = _≈_
DecTotalOrder._≤_ bytesDecTotalOrder = _≲_
DecTotalOrder.isDecTotalOrder bytesDecTotalOrder = bytesIsDecTotalOrder

open Data.List.Sort bytesDecTotalOrder public
