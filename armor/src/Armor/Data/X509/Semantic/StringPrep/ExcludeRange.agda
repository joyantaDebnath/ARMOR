{-# OPTIONS --sized-types #-}

open import Armor.Binary
open import Armor.Data.Unicode.UTF8
open import Armor.Data.Unicode.UTF8.Serializer
open import Armor.Prelude

import      Data.Vec.Relation.Unary.All as VecAll
import      Data.Vec.Properties         as Vec

module Armor.Data.X509.Semantic.StringPrep.ExcludeRange where

InRangeAndFilterElemSpec : ℕ × ℕ × Σ (ℕ → Set) Decidable → UInt8 → Set
InRangeAndFilterElemSpec (l , u , (P , _)) c = InRange l u c × P (toℕ c)

InRangeAndFilter
  : (s : ℕ) (spec : Vec (ℕ × ℕ × Σ (ℕ → Set) Decidable) s)
    → {@0 bs : List UInt8} → UTF8Char bs → Set₁
InRangeAndFilter s spec c =
  let xs = serializeUTF8Char' c
  in length xs ≡ s × All (uncurry InRangeAndFilterElemSpec) (zip (Vec.toList spec) xs)

inRangeAndFilter?
  : ∀ s → (spec : Vec (ℕ × ℕ × Σ (ℕ → Set) Decidable) s)
    → ∀ {@0 bs}
    → Decidable (InRangeAndFilter s spec {bs})
inRangeAndFilter? s spec c
  with serializeUTF8Char' c
... | xs'
  with length xs' ≟ s
... | no ¬len≡ =
  no λ where
    (len≡ , _) → contradiction len≡ ¬len≡
... | yes len≡
  with All.all? pf (zip (Vec.toList spec) xs')
  where
  pf : Decidable (uncurry InRangeAndFilterElemSpec)
  pf ((l , u , _ , d) , c) = inRange? l u c ×-dec d (toℕ c)
... | no ¬pf =
  no λ where
    (_ , pf) → contradiction pf ¬pf
... | yes pf =
  yes (len≡ , pf)
