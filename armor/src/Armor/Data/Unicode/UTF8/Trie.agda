{-# OPTIONS --sized-types --inversion-max-depth=1000 #-}

open import Armor.Binary
open import Armor.Prelude
  hiding (tabulate)
open import Armor.Data.Unicode.UTF8.TCB
import      Armor.Grammar.IList
import      Data.Fin.Properties as Fin
open import      Armor.Grammar.IList
import      Data.List.Relation.Binary.Equality.Propositional as List
import      Data.Nat.Properties as Nat

module Armor.Data.Unicode.UTF8.Trie where

open        Armor.Grammar.IList UInt8
open import Data.Trie (Fin.<-strictTotalOrder 256) as Trie public
open import Data.Tree.AVL.Value (List.≋-setoid{A = UInt8}) as Value public
  hiding (const)

UTF8TrieValue : Value _
UTF8TrieValue = Value.const (Exists─ (List UInt8) UTF8)

UTF8Trie : Set
UTF8Trie = Trie UTF8TrieValue _

lookupUTF8Trie = Trie.lookup

tabulateUTF8Trie : ∀ {n} → (Fin n → ∃ (Value.family UTF8TrieValue)) → UTF8Trie
tabulateUTF8Trie f = fromList (Vec.toList (Vec.tabulate f))

private
  inRangeLemmaᵤ : ∀ {l u} (p : Σ[ n ∈ ℕ ] InRange l u n) → {wit : True (u <? 256)} → proj₁ p < 256
  inRangeLemmaᵤ p {wit} = Nat.≤-trans (s≤s $ proj₂ (proj₂ p)) (toWitness wit)

{-
mapUTF8Char2ByShiftUp
  : (prefix₁ prefix₂ : Σ[ n ∈ ℕ ] InRange 192 223 n)
    → (range offset : Fin 32)
    → (lower : Σ[ n ∈ ℕ ] InRange 128 (191 - toℕ range - toℕ offset) n)
    → UTF8Trie
mapUTF8Char2ByShiftUp p₁ p₂ r o l = tabulateUTF8Trie mkEntry
  where
  open Nat.≤-Reasoning
  mkEntry : Fin (toℕ r) → List UInt8 × Exists─ (List UInt8) UTF8
  proj₁ (mkEntry i) =
    Fin.fromℕ< (inRangeLemmaᵤ p₁)
    ∷ [ Fin.fromℕ<{m = proj₁ l + toℕ i}
          (s≤s $ begin
            (proj₁ l + toℕ i)
              ≤⟨ Nat.+-monoˡ-≤ (toℕ i) (proj₂ (proj₂ l)) ⟩
            (191 - toℕ r - toℕ o) + toℕ i
              ≤⟨ Nat.+-monoʳ-≤ (191 - toℕ r - toℕ o) (Fin.toℕ≤n i) ⟩
            191 - toℕ r - toℕ o + toℕ r
              ≤⟨ Nat.+-monoˡ-≤ (toℕ r) (begin
                191 - toℕ r - toℕ o ≤⟨ Nat.∸-monoʳ-≤ {n = toℕ o} (191 - toℕ r) z≤n ⟩
                191 - toℕ r          ≤⟨ Nat.m∸n≤m 191 (toℕ r) ⟩
                191 ∎) ⟩
            191 + toℕ r
              ≤⟨ Nat.+-monoʳ-≤ 191 (Fin.toℕ≤n r) ⟩
            191 + 32
              ≤⟨ toWitness{Q = 191 + 32 ≤? 255} tt ⟩
            255 ∎) ]
  -- cons (mkIListCons (utf82 (mkUTF8Char2 b₁ b₂ b₁range b₂range refl)) nil refl)    
  proj₂ (mkEntry i) = {!!} , {!!}
    where
    b₁ : UInt8
    b₁ = Fin.fromℕ< (inRangeLemmaᵤ p₂)

    b₁range : InRange 192 223 b₁
    b₁range = subst (InRange 192 223) (sym (Fin.toℕ-fromℕ< (inRangeLemmaᵤ p₂))) (proj₂ p₂)

    b₂ℕ : ℕ
    b₂ℕ = proj₁ l + toℕ o + toℕ i

    b₂ℕrange : InRange 128 191 b₂ℕ
    proj₁ b₂ℕrange = begin
      128 ≤⟨ proj₁ (proj₂ l) ⟩
      proj₁ l ≤⟨ Nat.m≤m+n (proj₁ l) (toℕ o) ⟩
      proj₁ l + toℕ o ≤⟨ Nat.m≤m+n (proj₁ l + toℕ o) (toℕ i) ⟩
      (proj₁ l + toℕ o) + toℕ i ∎
    proj₂ b₂ℕrange = begin
      proj₁ l + toℕ o + toℕ i ≡⟨ Nat.+-assoc (proj₁ l) (toℕ o) (toℕ i) ⟩
      proj₁ l + (toℕ o + toℕ i) ≤⟨ Nat.+-monoˡ-≤ (toℕ o + toℕ i) (proj₂ (proj₂ l)) ⟩
      (191 - toℕ r - toℕ o) + (toℕ o + toℕ i) ≡⟨ cong (_+ (toℕ o + toℕ i)) (Nat.∸-+-assoc 191 (toℕ r) (toℕ o)) ⟩
      191 - (toℕ r + toℕ o) + (toℕ o + toℕ i) ≡⟨ cong (λ x → 191 - x + (toℕ o + toℕ i)) (Nat.+-comm (toℕ r) (toℕ o)) ⟩
      191 - (toℕ o + toℕ r) + (toℕ o + toℕ i) ≤⟨ Nat.+-monoʳ-≤ (191 - (toℕ o + toℕ r))
                                                   (Nat.+-monoʳ-≤ (toℕ o) (Fin.toℕ≤n i)) ⟩
      191 - (toℕ o + toℕ r) + (toℕ o + toℕ r)
        ≡⟨ sym (Nat.+-∸-comm (toℕ o + toℕ r)
             (begin
               toℕ o + toℕ r ≤⟨ Nat.+-mono-≤ (Fin.toℕ≤n o) (Fin.toℕ≤n r) ⟩
               32 + 32 ≤⟨ toWitness{Q = 64 ≤? 191} tt ⟩
               191 ∎))
         ⟩
      191 + (toℕ o + toℕ r) - (toℕ o + toℕ r) ≡⟨ Nat.+-∸-assoc 191 (Nat.≤-refl{x = toℕ o + toℕ r}) ⟩
      191 + ((toℕ o + toℕ r) - (toℕ o + toℕ r)) ≡⟨ cong (191 +_) (Nat.n∸n≡0 (toℕ o + toℕ r)) ⟩
      191 - 0 ≡⟨ Nat.+-identityʳ 191 ⟩
      191 ∎

    b₂ : UInt8
    b₂ = Fin.fromℕ< (inRangeLemmaᵤ (b₂ℕ , b₂ℕrange))

    b₂range : InRange 128 191 b₂
    b₂range = subst (InRange 128 191) (sym (Fin.toℕ-fromℕ< (inRangeLemmaᵤ (b₂ℕ , b₂ℕrange)))) b₂ℕrange
-}
