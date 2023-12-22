open import Armor.Binary
open import Armor.Data.X690-DER.BitString.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Serializer
open import Armor.Prelude
import      Data.Nat.Properties as Nat

module Armor.Data.X690-DER.BitString.Serializer where

open Armor.Grammar.Serializer UInt8

private
  serializeValueRaw : List Bool → UInt8 × List UInt8
  serializeValueRaw [] = # 0 , []
  serializeValueRaw (x₀ ∷ [])                                = # 7 , [ fromBinary (                              Vec.[ x₀ ] Vec.++ Vec.replicate{n = 7} #0) ]
  serializeValueRaw (x₀ ∷ x₁ ∷ [])                           = # 6 , [ fromBinary (x₀ ∷                          Vec.[ x₁ ] Vec.++ Vec.replicate{n = 6} #0) ]
  serializeValueRaw (x₀ ∷ x₁ ∷ x₂ ∷ [])                      = # 5 , [ fromBinary (x₀ ∷ x₁ ∷                     Vec.[ x₂ ] Vec.++ Vec.replicate{n = 5} #0) ]
  serializeValueRaw (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ [])                 = # 4 , [ fromBinary (x₀ ∷ x₁ ∷ x₂ ∷                Vec.[ x₃ ] Vec.++ Vec.replicate{n = 4} #0) ]
  serializeValueRaw (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ [])            = # 3 , [ fromBinary (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷           Vec.[ x₄ ] Vec.++ Vec.replicate{n = 3} #0) ]
  serializeValueRaw (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])       = # 2 , [ fromBinary (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷      Vec.[ x₅ ] Vec.++ Vec.replicate{n = 2} #0) ]
  serializeValueRaw (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ [])  = # 1 , [ fromBinary (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ Vec.[ x₆ ] Vec.++ Vec.replicate{n = 1} #0) ]
  serializeValueRaw (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ x₇ ∷ xs) =
    let b         = fromBinary (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ Vec.[ x₇ ])
        (bₕ , bₜ) = serializeValueRaw xs
    in bₕ , b ∷ bₜ

  @0 serializeValueRaw≡ : ∀ (bits : List Bool) {bₕ bₜ} → (bₕ<8 : toℕ bₕ < 8) (bits≡ : bits ≡ toBitRep bₕ bₜ) (u : UnusedBits bₕ bₜ)
                          → let (bₕ' , bₜ') = serializeValueRaw bits in _≡_{A = List UInt8} (bₕ' ∷ bₜ') (bₕ ∷ bₜ)
  serializeValueRaw≡ [] {bₕ} {[]} bₕ<8 bits≡ u =
    cong₂ _∷_ (Fin.toℕ-injective (sym u)) refl
  serializeValueRaw≡ [] {bₕ} {x ∷ []} bₕ<8 bits≡ u =
    contradiction{P = length xs' ≡ 0}
      (cong length (sym bits≡))
      (Nat.>⇒≢ xs'Len>)
    where
    open ≡-Reasoning
    module ≤ = Nat.≤-Reasoning

    xs = Vec.toList (toBinary{8} x)
    xs' = take (8 - toℕ bₕ) xs

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x)

    xs'Len : length xs' ≡ 8 - toℕ bₕ
    xs'Len = begin
      length xs' ≡⟨ length-take (8 - toℕ bₕ) xs ⟩
      (8 - toℕ bₕ) ⊓ length xs ≡⟨ cong ((8 ∸ toℕ bₕ) ⊓_) xsLen ⟩
      (8 - toℕ bₕ) ⊓ 8 ≡⟨ Nat.m≤n⇒m⊓n≡m (Nat.m∸n≤m 8 (toℕ bₕ)) ⟩
      8 - toℕ bₕ ∎

    xs'Len> : length xs' > 0
    xs'Len> = ≤.begin
      (1 ≤.≤⟨ Nat.m<n⇒0<n∸m bₕ<8 ⟩
      8 - toℕ bₕ ≤.≡⟨ sym xs'Len ⟩
      length xs' ≤.∎)

  serializeValueRaw≡ [] {bₕ} {x ∷ x₁ ∷ bₜ} bₕ<8 bits≡ u =
    contradiction{P = 0 ≥ 8}
      (Nat.≤-trans xsLen> (Lemmas.≡⇒≤ (sym $ cong length bits≡)))
      λ ()
    where
    module ≤ = Nat.≤-Reasoning

    xs₁ = Vec.toList (toBinary{8} x)
    xs₂ = toBitRep bₕ (x₁ ∷ bₜ)

    xs = xs₁ ++ xs₂

    xs₁Len : length xs₁ ≡ 8
    xs₁Len = Lemmas.toListLength (toBinary{8} x)

    xsLen> : length xs ≥ 8
    xsLen> = ≤.begin
      8 ≤.≡⟨ sym xs₁Len ⟩
      length xs₁ ≤.≤⟨ Nat.m≤m+n (length xs₁) (length xs₂) ⟩
      length xs₁ + length xs₂ ≤.≡⟨ sym (length-++ xs₁ {xs₂}) ⟩
      length (xs₁ ++ xs₂) ≤.∎

  serializeValueRaw≡ (x ∷ []) {bₕ} {x₁ ∷ []} bₕ<8 bits≡ u =
    cong₂ _∷_ (Fin.toℕ-injective (sym bₕ≡7))
      (cong [_] (sym (begin
        (x₁ ≡⟨ sym (fromBinary∘toBinary{8} x₁) ⟩
        fromBinary (toBinary{8} x₁)
          ≡⟨ cong fromBinary (Lemmas.toList-injective (toBinary{8} x₁) (x ∷ Vec.replicate #0) (begin
               xs ≡⟨ sym (take++drop (8 - toℕ bₕ) xs) ⟩
               take (8 - toℕ bₕ) xs ++ drop (8 - toℕ bₕ) xs ≡⟨ cong₂ _++_ (sym bits≡) u ⟩
               x ∷ replicate (toℕ bₕ) #0 ≡⟨ cong (λ y → x ∷ replicate y #0) bₕ≡7 ⟩
               x ∷ replicate 7 #0 ∎))
           ⟩
        _ ∎))))
    where
    open ≡-Reasoning

    xs  = Vec.toList (toBinary{8} x₁)
    xs' = take (8 - toℕ bₕ) xs

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x₁)

    8-bₕ≡1 : 8 - toℕ bₕ ≡ 1
    8-bₕ≡1 = begin
      (8 - toℕ bₕ ≡⟨ sym (Nat.m≤n⇒m⊓n≡m (Nat.m∸n≤m _ (toℕ bₕ))) ⟩
      (8 - toℕ bₕ) ⊓ 8 ≡⟨ cong ((8 ∸ toℕ bₕ) ⊓_) (sym xsLen) ⟩
      (8 - toℕ bₕ) ⊓ length xs ≡⟨ (sym $ length-take (8 - toℕ bₕ) xs) ⟩
      length xs' ≡⟨ sym (cong length bits≡) ⟩
      1 ∎)

    bₕ≡7 : toℕ bₕ ≡ 7
    bₕ≡7 = Nat.∸-cancelˡ-≡ (Nat.<⇒≤ bₕ<8) (toWitness{Q = _ ≤? _} tt) 8-bₕ≡1

    xs≡ : xs ≡ x ∷ replicate 7 #0
    xs≡ = begin
      xs ≡⟨ sym (take++drop 1 xs) ⟩
      take 1 xs ++ drop 1 xs ≡⟨ cong (λ x → take (8 - x) xs ++ drop (8 - x) xs) (sym bₕ≡7) ⟩
      xs' ++ drop (8 - toℕ bₕ) xs ≡⟨ cong₂ _++_ (sym bits≡) u ⟩
      x ∷ replicate (toℕ bₕ) #0 ≡⟨ cong (λ y → x ∷ replicate y #0) bₕ≡7 ⟩
      x ∷ replicate 7 #0 ∎

  serializeValueRaw≡ (x ∷ []) {bₕ} {x₁ ∷ x₂ ∷ bₜ} bₕ<8 bits≡ u =
    contradiction{P = 1 ≥ 8}
      (≤.begin
        8 ≤.≡⟨ sym xsLen ⟩
        length xs ≤.≤⟨ Nat.m≤m+n (length xs) _ ⟩
        length xs + length (toBitRep bₕ (x₂ ∷ bₜ)) ≤.≡⟨ sym (length-++ xs {toBitRep bₕ (x₂ ∷ bₜ)}) ⟩
        length (xs ++ toBitRep bₕ (x₂ ∷ bₜ)) ≤.≡⟨ cong length (sym bits≡) ⟩
        (length [ x ]) ≤.≡⟨⟩
        1 ≤.∎)
      λ where (s≤s ())
    where
    import Data.Nat.Properties as Nat
    module ≤ = Nat.≤-Reasoning

    xs = Vec.toList (toBinary{8} x₁)

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x₁)

    
  serializeValueRaw≡ (x ∷ x₁ ∷ []) {bₕ} {x₂ ∷ []} bₕ<8 bits≡ u =
    cong₂ _∷_ (Fin.toℕ-injective (sym bₕ≡6))
      (cong [_] (sym (begin
        (x₂ ≡⟨ sym (fromBinary∘toBinary{8} x₂) ⟩
        fromBinary (toBinary{8} x₂)
          ≡⟨ cong fromBinary (Lemmas.toList-injective (toBinary{8} x₂) (x ∷ x₁ ∷ Vec.replicate #0)
               (begin
                 xs ≡⟨ sym (take++drop (8 - toℕ bₕ) xs) ⟩
                 take (8 - toℕ bₕ) xs ++ drop (8 - toℕ bₕ) xs ≡⟨ cong₂ _++_ (sym bits≡) u ⟩
                 x ∷ x₁ ∷ replicate (toℕ bₕ) #0 ≡⟨ cong (λ y → x ∷ x₁ ∷ replicate y #0) bₕ≡6 ⟩
                 x ∷ x₁ ∷ replicate 6 #0 ∎))
           ⟩
        _ ∎))))
    where
    open ≡-Reasoning

    xs = Vec.toList (toBinary{8} x₂)
    xs' = take (8 - toℕ bₕ) xs

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x₂)

    8-bₕ≡2 : 8 - toℕ bₕ ≡ 2
    8-bₕ≡2 = begin
      (8 - toℕ bₕ ≡⟨ sym (Nat.m≤n⇒m⊓n≡m (Nat.m∸n≤m _ (toℕ bₕ))) ⟩
      (8 - toℕ bₕ) ⊓ 8 ≡⟨ cong ((8 ∸ toℕ bₕ) ⊓_) (sym xsLen) ⟩
      (8 - toℕ bₕ) ⊓ length xs ≡⟨ (sym $ length-take (8 - toℕ bₕ) xs) ⟩
      length xs' ≡⟨ sym (cong length bits≡) ⟩
      2 ∎)

    bₕ≡6 : toℕ bₕ ≡ 6
    bₕ≡6 = Nat.∸-cancelˡ-≡ (Nat.<⇒≤ bₕ<8) (toWitness{Q = _ ≤? _} tt) 8-bₕ≡2

    xs≡ : xs ≡ x ∷ x₁ ∷ replicate 6 #0
    xs≡ = begin
      xs ≡⟨ sym (take++drop 2 xs) ⟩
      take 2 xs ++ drop 2 xs ≡⟨ cong (λ x → take (8 - x) xs ++ drop (8 - x) xs) (sym bₕ≡6) ⟩
      xs' ++ drop (8 - toℕ bₕ) xs ≡⟨ cong₂ _++_ (sym bits≡) u ⟩
      x ∷ x₁ ∷ replicate (toℕ bₕ) #0 ≡⟨ cong (λ y → x ∷ x₁ ∷ replicate y #0) bₕ≡6 ⟩
      x ∷ x₁ ∷ replicate 6 #0 ∎

  serializeValueRaw≡ (x ∷ x₁ ∷ []) {bₕ} {x₂ ∷ x₃ ∷ bₜ} bₕ<8 bits≡ u =
    contradiction{P = 2 ≥ 8}
      (≤.begin
        8 ≤.≡⟨ sym xsLen ⟩
        length xs ≤.≤⟨ Nat.m≤m+n (length xs) _ ⟩
        length xs + length (toBitRep bₕ (x₃ ∷ bₜ)) ≤.≡⟨ sym (length-++ xs {toBitRep bₕ (x₃ ∷ bₜ)}) ⟩
        length (xs ++ toBitRep bₕ (x₃ ∷ bₜ)) ≤.≡⟨ cong length (sym bits≡) ⟩
        length (x ∷ [ x₁ ]) ≤.≡⟨⟩
        2 ≤.∎)
      λ where (s≤s (s≤s ()))
    where
    import Data.Nat.Properties as Nat
    module ≤ = Nat.≤-Reasoning

    xs = Vec.toList (toBinary{8} x₂)

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x₂)

  serializeValueRaw≡ (x ∷ x₁ ∷ x₂ ∷ []) {bₕ} {x₃ ∷ []} bₕ<8 bits≡ u =
    cong₂ _∷_ (Fin.toℕ-injective (sym bₕ≡5))
      (cong [_] (sym ∘ begin_ $
        x₃ ≡⟨ sym (fromBinary∘toBinary{8} x₃) ⟩
        fromBinary (toBinary{8} x₃)
          ≡⟨ cong fromBinary
               (Lemmas.toList-injective
                 (toBinary {8} x₃)
                 (x ∷ x₁ ∷ x₂ ∷ Vec.replicate #0)
                 xs≡)
          ⟩
        _ ∎))
    where
    open ≡-Reasoning

    xs = Vec.toList (toBinary{8} x₃)
    xs' = take (8 - toℕ bₕ) xs

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x₃)

    8-bₕ≡3 : 8 - toℕ bₕ ≡ 3
    8-bₕ≡3 = begin
      (8 - toℕ bₕ ≡⟨ sym (Nat.m≤n⇒m⊓n≡m (Nat.m∸n≤m _ (toℕ bₕ))) ⟩
      (8 - toℕ bₕ) ⊓ 8 ≡⟨ cong ((8 ∸ toℕ bₕ) ⊓_) (sym xsLen) ⟩
      (8 - toℕ bₕ) ⊓ length xs ≡⟨ (sym $ length-take (8 - toℕ bₕ) xs) ⟩
      length xs' ≡⟨ sym (cong length bits≡) ⟩
      3 ∎)

    bₕ≡5 : toℕ bₕ ≡ 5
    bₕ≡5 = Nat.∸-cancelˡ-≡ (Nat.<⇒≤ bₕ<8) (toWitness{Q = _ ≤? _} tt) 8-bₕ≡3

    xs≡ : xs ≡ x ∷ x₁ ∷ x₂ ∷ replicate 5 #0
    xs≡ = begin
      xs ≡⟨ sym (take++drop 3 xs) ⟩
      take 3 xs ++ drop 3 xs ≡⟨ cong (λ x → take (8 - x) xs ++ drop (8 - x) xs) (sym bₕ≡5) ⟩
      xs' ++ drop (8 - toℕ bₕ) xs ≡⟨ cong₂ _++_ (sym bits≡) u ⟩
      x ∷ x₁ ∷ x₂ ∷ replicate (toℕ bₕ) #0 ≡⟨ cong (λ y → x ∷ x₁ ∷ x₂ ∷ replicate y #0) bₕ≡5 ⟩
      x ∷ x₁ ∷ x₂ ∷ replicate 5 #0 ∎

  serializeValueRaw≡ (x ∷ x₁ ∷ x₂ ∷ []) {bₕ} {x₃ ∷ x₄ ∷ bₜ} bₕ<8 bits≡ u =
    contradiction {P = 3 ≥ 8}
      (≤.begin
        8 ≤.≡⟨ sym xsLen ⟩
        length xs ≤.≤⟨ Nat.m≤m+n (length xs) (length xs') ⟩
        length xs + length xs' ≤.≡⟨ sym (length-++ xs {xs'}) ⟩
        length (xs ++ xs') ≤.≡⟨ cong length (sym bits≡) ⟩
        length (x ∷ x₁ ∷ [ x₂ ]) ≤.∎)
      (λ { (s≤s (s≤s (s≤s ())))})
    where
    module ≤ = Nat.≤-Reasoning

    xs = Vec.toList (toBinary{8} x₃)

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x₃)

    xs' = toBitRep bₕ (x₄ ∷ bₜ)

  serializeValueRaw≡ (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) {bₕ} {x₄ ∷ []} bₕ<8 bits≡ u =
    cong₂ _∷_ (Fin.toℕ-injective (sym bₕ≡4))
      (cong [_] (sym ∘ begin_ $
        x₄ ≡⟨ sym (fromBinary∘toBinary{8} x₄) ⟩
        fromBinary (toBinary{8} x₄)
          ≡⟨ cong fromBinary
               (Lemmas.toList-injective
                 (toBinary {8} x₄)
                 (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ Vec.replicate #0)
                 xs≡)
          ⟩
        _ ∎))

    where
    open ≡-Reasoning

    xs = Vec.toList (toBinary{8} x₄)
    xs' = take (8 - toℕ bₕ) xs

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x₄)

    8-bₕ≡4 : 8 - toℕ bₕ ≡ 4
    8-bₕ≡4 = begin
      (8 - toℕ bₕ ≡⟨ sym (Nat.m≤n⇒m⊓n≡m (Nat.m∸n≤m _ (toℕ bₕ))) ⟩
      (8 - toℕ bₕ) ⊓ 8 ≡⟨ cong ((8 ∸ toℕ bₕ) ⊓_) (sym xsLen) ⟩
      (8 - toℕ bₕ) ⊓ length xs ≡⟨ (sym $ length-take (8 - toℕ bₕ) xs) ⟩
      length xs' ≡⟨ sym (cong length bits≡) ⟩
      4 ∎)

    bₕ≡4 : toℕ bₕ ≡ 4
    bₕ≡4 = Nat.∸-cancelˡ-≡ (Nat.<⇒≤ bₕ<8) (toWitness{Q = _ ≤? _} tt) 8-bₕ≡4

    xs≡ : xs ≡ x ∷ x₁ ∷ x₂ ∷ x₃ ∷ replicate 4 #0
    xs≡ = begin
      xs ≡⟨ sym (take++drop 4 xs) ⟩
      take 4 xs ++ drop 4 xs ≡⟨ cong (λ x → take (8 - x) xs ++ drop (8 - x) xs) (sym bₕ≡4) ⟩
      xs' ++ drop (8 - toℕ bₕ) xs ≡⟨ cong₂ _++_ (sym bits≡) u ⟩
      x ∷ x₁ ∷ x₂ ∷ x₃ ∷ replicate (toℕ bₕ) #0
        ≡⟨ cong (λ y → x ∷ x₁ ∷ x₂ ∷ x₃ ∷ replicate y #0) bₕ≡4 ⟩
      x ∷ x₁ ∷ x₂ ∷ x₃ ∷ replicate 4 #0 ∎


  serializeValueRaw≡ (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) {bₕ} {x₄ ∷ x₅ ∷ bₜ} bₕ<8 bits≡ u =
    contradiction{P = 4 ≥ 8}
      (≤.begin
        8 ≤.≡⟨ sym xsLen ⟩
        length xs ≤.≤⟨ Nat.m≤m+n (length xs) (length xs') ⟩
        length xs + length xs' ≤.≡⟨ sym (length-++ xs {xs'}) ⟩
        length (xs ++ xs') ≤.≡⟨ cong length (sym bits≡) ⟩
        length (x ∷ x₁ ∷ x₂ ∷ [ x₃ ]) ≤.∎)
      (toWitnessFalse{Q = _ ≤? _} tt)
    where
    module ≤ = Nat.≤-Reasoning

    xs = Vec.toList (toBinary{8} x₄)

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x₄)

    xs' = toBitRep bₕ (x₅ ∷ bₜ)

  serializeValueRaw≡ (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ []) {bₕ} {x₅ ∷ []} bₕ<8 bits≡ u =
    cong₂ _∷_ (Fin.toℕ-injective (sym bₕ≡3))
      (cong [_] (sym ∘ begin_ $
        x₅ ≡⟨ sym (fromBinary∘toBinary{8} x₅) ⟩
        fromBinary (toBinary{8} x₅)
          ≡⟨ cong fromBinary
               (Lemmas.toList-injective
                 (toBinary {8} x₅)
                 (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ Vec.replicate #0)
                 xs≡)
          ⟩
        _ ∎))
    where
    open ≡-Reasoning

    xs = Vec.toList (toBinary{8} x₅)
    xs' = take (8 - toℕ bₕ) xs

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x₅)

    8-bₕ≡3 : 8 - toℕ bₕ ≡ 5
    8-bₕ≡3 = begin
      (8 - toℕ bₕ ≡⟨ sym (Nat.m≤n⇒m⊓n≡m (Nat.m∸n≤m _ (toℕ bₕ))) ⟩
      (8 - toℕ bₕ) ⊓ 8 ≡⟨ cong ((8 ∸ toℕ bₕ) ⊓_) (sym xsLen) ⟩
      (8 - toℕ bₕ) ⊓ length xs ≡⟨ (sym $ length-take (8 - toℕ bₕ) xs) ⟩
      length xs' ≡⟨ sym (cong length bits≡) ⟩
      5 ∎)

    bₕ≡3 : toℕ bₕ ≡ 3
    bₕ≡3 = Nat.∸-cancelˡ-≡ (Nat.<⇒≤ bₕ<8) (toWitness{Q = _ ≤? _} tt) 8-bₕ≡3

    xs≡ : xs ≡ x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ replicate 3 #0
    xs≡ = begin
      xs ≡⟨ sym (take++drop 5 xs) ⟩
      take 5 xs ++ drop 5 xs ≡⟨ cong (λ x → take (8 - x) xs ++ drop (8 - x) xs) (sym bₕ≡3) ⟩
      xs' ++ drop (8 - toℕ bₕ) xs ≡⟨ cong₂ _++_ (sym bits≡) u ⟩
      x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ replicate (toℕ bₕ) #0
        ≡⟨ cong (λ y → x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ replicate y #0) bₕ≡3 ⟩
      x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ replicate 3 #0 ∎

  serializeValueRaw≡ (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ []) {bₕ} {x₅ ∷ x₆ ∷ bₜ} bₕ<8 bits≡ u =
    contradiction{P = 5 ≥ 8}
      (≤.begin
        8 ≤.≡⟨ sym xsLen ⟩
        length xs ≤.≤⟨ Nat.m≤m+n (length xs) (length xs') ⟩
        length xs + length xs' ≤.≡⟨ sym (length-++ xs {xs'}) ⟩
        length (xs ++ xs') ≤.≡⟨ cong length (sym bits≡) ⟩
        length (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ [ x₄ ]) ≤.∎)
      (toWitnessFalse{Q = _ ≤? _} tt)
    where
    module ≤ = Nat.≤-Reasoning

    xs = Vec.toList (toBinary{8} x₅)

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x₅)

    xs' = toBitRep bₕ (x₆ ∷ bₜ)

  serializeValueRaw≡ (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) {bₕ} {x₆ ∷ []} bₕ<8 bits≡ u =
    cong₂ _∷_ (Fin.toℕ-injective (sym bₕ≡2))
      (cong [_] (sym ∘ begin_ $
        x₆ ≡⟨ sym (fromBinary∘toBinary{8} x₆) ⟩
        fromBinary (toBinary{8} x₆)
          ≡⟨ cong fromBinary
               (Lemmas.toList-injective
                 (toBinary {8} x₆)
                 (Vec.fromList xs“ Vec.++ Vec.replicate #0)
                 xs≡)
          ⟩
        _ ∎))

    where
    open ≡-Reasoning

    xs = Vec.toList (toBinary{8} x₆)
    xs' = take (8 - toℕ bₕ) xs
    xs“ = x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x₆)

    8-bₕ≡2 : 8 - toℕ bₕ ≡ 6
    8-bₕ≡2 = begin
      (8 - toℕ bₕ ≡⟨ sym (Nat.m≤n⇒m⊓n≡m (Nat.m∸n≤m _ (toℕ bₕ))) ⟩
      (8 - toℕ bₕ) ⊓ 8 ≡⟨ cong ((8 ∸ toℕ bₕ) ⊓_) (sym xsLen) ⟩
      (8 - toℕ bₕ) ⊓ length xs ≡⟨ (sym $ length-take (8 - toℕ bₕ) xs) ⟩
      length xs' ≡⟨ sym (cong length bits≡) ⟩
      _ ∎)

    bₕ≡2 : toℕ bₕ ≡ 2
    bₕ≡2 = Nat.∸-cancelˡ-≡ (Nat.<⇒≤ bₕ<8) (toWitness{Q = _ ≤? _} tt) 8-bₕ≡2

    xs≡ : xs ≡ xs“ ++ replicate 2 #0
    xs≡ = begin
      xs ≡⟨ sym (take++drop 6 xs) ⟩
      take 6 xs ++ drop 6 xs ≡⟨ cong (λ x → take (8 - x) xs ++ drop (8 - x) xs) (sym bₕ≡2) ⟩
      xs' ++ drop (8 - toℕ bₕ) xs ≡⟨ cong₂ _++_ (sym bits≡) u ⟩
      xs“ ++ replicate (toℕ bₕ) #0
        ≡⟨ cong (λ y → xs“ ++ replicate y #0) bₕ≡2 ⟩
      _ ∎

  serializeValueRaw≡ (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) {bₕ} {x₆ ∷ x₇ ∷ bₜ} bₕ<8 bits≡ u =
    contradiction{P = 6 ≥ 8}
      (≤.begin
        8 ≤.≡⟨ sym xsLen ⟩
        length xs ≤.≤⟨ Nat.m≤m+n (length xs) (length xs') ⟩
        length xs + length xs' ≤.≡⟨ sym (length-++ xs {xs'}) ⟩
        length (xs ++ xs') ≤.≡⟨ cong length (sym bits≡) ⟩
        length xs“ ≤.∎)
      (toWitnessFalse{Q = _ ≤? _} tt)
    where
    module ≤ = Nat.≤-Reasoning

    xs = Vec.toList (toBinary{8} x₆)

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x₆)

    xs' = toBitRep bₕ (x₇ ∷ bₜ)
    xs“ = x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []

  serializeValueRaw≡ (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ []) {bₕ} {x₇ ∷ []} bₕ<8 bits≡ u =
    cong₂ _∷_ (Fin.toℕ-injective (sym bₕ≡1))
      (cong [_] (sym ∘ begin_ $
        x₇ ≡⟨ sym (fromBinary∘toBinary{8} x₇) ⟩
        fromBinary (toBinary{8} x₇)
          ≡⟨ cong fromBinary
               (Lemmas.toList-injective
                 (toBinary {8} x₇)
                 (Vec.fromList xs“ Vec.++ Vec.replicate #0)
                 xs≡)
          ⟩
        _ ∎))

    where
    open ≡-Reasoning

    xs = Vec.toList (toBinary{8} x₇)
    xs' = take (8 - toℕ bₕ) xs
    xs“ = x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ []

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x₇)

    8-bₕ≡1 : 8 - toℕ bₕ ≡ 7
    8-bₕ≡1 = begin
      (8 - toℕ bₕ ≡⟨ sym (Nat.m≤n⇒m⊓n≡m (Nat.m∸n≤m _ (toℕ bₕ))) ⟩
      (8 - toℕ bₕ) ⊓ 8 ≡⟨ cong ((8 ∸ toℕ bₕ) ⊓_) (sym xsLen) ⟩
      (8 - toℕ bₕ) ⊓ length xs ≡⟨ (sym $ length-take (8 - toℕ bₕ) xs) ⟩
      length xs' ≡⟨ sym (cong length bits≡) ⟩
      _ ∎)

    bₕ≡1 : toℕ bₕ ≡ 1
    bₕ≡1 = Nat.∸-cancelˡ-≡ (Nat.<⇒≤ bₕ<8) (toWitness{Q = _ ≤? _} tt) 8-bₕ≡1

    xs≡ : xs ≡ xs“ ++ replicate 1 #0
    xs≡ = begin
      xs ≡⟨ sym (take++drop 7 xs) ⟩
      take 7 xs ++ drop 7 xs ≡⟨ cong (λ x → take (8 - x) xs ++ drop (8 - x) xs) (sym bₕ≡1) ⟩
      xs' ++ drop (8 - toℕ bₕ) xs ≡⟨ cong₂ _++_ (sym bits≡) u ⟩
      xs“ ++ replicate (toℕ bₕ) #0
        ≡⟨ cong (λ y → xs“ ++ replicate y #0) bₕ≡1 ⟩
      _ ∎

  serializeValueRaw≡ (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ []) {bₕ} {x₇ ∷ x₈ ∷ bₜ} bₕ<8 bits≡ u =
    contradiction{P = 7 ≥ 8}
      (≤.begin
        8 ≤.≡⟨ sym xsLen ⟩
        length xs ≤.≤⟨ Nat.m≤m+n (length xs) (length xs') ⟩
        length xs + length xs' ≤.≡⟨ sym (length-++ xs {xs'}) ⟩
        length (xs ++ xs') ≤.≡⟨ cong length (sym bits≡) ⟩
        length xs“ ≤.∎)
      (toWitnessFalse{Q = _ ≤? _} tt)
    where
    module ≤ = Nat.≤-Reasoning

    xs = Vec.toList (toBinary{8} x₇)

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x₇)

    xs' = toBitRep bₕ (x₈ ∷ bₜ)
    xs“ = x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ []
  serializeValueRaw≡ (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ x₇ ∷ bits) {bₕ} {x₈ ∷ []} bₕ<8 bits≡ u =
    cong₂ _∷_ (∷-injectiveˡ ih)
      (cong₂ _∷_
        (sym (begin
          x₈ ≡⟨ sym (fromBinary∘toBinary{8} x₈) ⟩
          fromBinary (toBinary{8} x₈)
            ≡⟨ cong fromBinary
                 (Lemmas.toList-injective (toBinary{8} x₈) (Vec.fromList xs“)
                   (begin xs ≡⟨ xs≡xs' ⟩
                          xs' ≡⟨ (sym $ proj₁ xs×bits≡) ⟩
                          xs“ ∎))
              ⟩
          fromBinary (Vec.fromList xs“) ∎))
        (∷-injectiveʳ ih))
    where
    open ≡-Reasoning
    module ≤ = Nat.≤-Reasoning

    xs = Vec.toList (toBinary{8} x₈)
    xs' = take (8 - toℕ bₕ) xs
    xs“ = x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ [ x₇ ]

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x₈)

    8-bₕ≤8 : 8 - toℕ bₕ ≤ 8
    8-bₕ≤8 = Nat.m∸n≤m 8 (toℕ bₕ)

    8-bₕ≥8 : 8 - toℕ bₕ ≥ 8
    8-bₕ≥8 = ≤.begin
      8 ≤.≤⟨ Nat.m≤m+n 8 (length bits) ⟩
      8 + length bits ≤.≡⟨ cong length bits≡ ⟩
      length xs' ≤.≡⟨ length-take (8 - toℕ bₕ) xs ⟩
      (8 - toℕ bₕ) ⊓ length xs ≤.≡⟨ cong ((8 ∸ toℕ bₕ) ⊓_) xsLen ⟩
      (8 - toℕ bₕ) ⊓ 8 ≤.≡⟨ Nat.m≤n⇒m⊓n≡m (Nat.m∸n≤m _ (toℕ bₕ)) ⟩ 
      8 - toℕ bₕ ≤.∎

    8-bₕ≡8 : 8 - toℕ bₕ ≡ 8
    8-bₕ≡8 = Nat.≤-antisym 8-bₕ≤8 8-bₕ≥8

    bₕ≡0 : toℕ bₕ ≡ 0
    bₕ≡0 = Nat.∸-cancelˡ-≡ (Nat.<⇒≤ bₕ<8) (toWitness{Q = _ ≤? _} tt) 8-bₕ≡8

    xs≡xs' : xs ≡ xs'
    xs≡xs' = begin
      xs ≡⟨ sym (take++drop 8 xs) ⟩
      take 8 xs ++ drop 8 xs ≡⟨ cong (_++ drop 8 xs) (cong (λ x → take x xs) (sym 8-bₕ≡8)) ⟩
      xs' ++ drop 8 xs ≡⟨ cong (xs' ++_) (cong (λ x → drop x xs) (sym xsLen)) ⟩
      xs' ++ drop (length xs) xs ≡⟨ cong (xs' ++_) (Lemmas.drop-length xs) ⟩
      xs' ++ [] ≡⟨ ++-identityʳ xs' ⟩
      xs' ∎

    xs≡' : xs ≡ xs“ ++ bits
    xs≡' = trans xs≡xs' (sym bits≡)

    xs×bits≡ : xs“ ≡ xs' × bits ≡ []
    xs×bits≡ = Lemmas.length-++-≡ xs“ bits xs' []
                 (begin
                   xs“ ++ bits ≡⟨ sym xs≡' ⟩
                   xs ≡⟨ xs≡xs' ⟩
                   xs' ≡⟨ sym (++-identityʳ xs') ⟩
                   xs' ++ [] ∎)
                 (begin
                   length xs“ ≡⟨⟩
                   8 ≡⟨ sym 8-bₕ≡8 ⟩
                   (8 - toℕ bₕ) ≡⟨ sym (Nat.m≤n⇒m⊓n≡m (Nat.m∸n≤m 8 (toℕ bₕ))) ⟩
                   (8 - toℕ bₕ) ⊓ 8 ≡⟨ cong ((8 ∸ toℕ bₕ) ⊓_) (sym xsLen) ⟩
                   (8 - toℕ bₕ) ⊓ length xs ≡⟨ sym (length-take (8 ∸ toℕ bₕ) xs) ⟩
                   length xs' ∎)

    ih = serializeValueRaw≡ bits{bₕ}{[]} bₕ<8 (proj₂ xs×bits≡) bₕ≡0

  serializeValueRaw≡ (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ x₇ ∷ bits) {bₕ} {x₈ ∷ x₉ ∷ bₜ} bₕ<8 bits≡ u =
    cong₂ _∷_
      (∷-injectiveˡ ih)
      (cong₂ _∷_
        (sym (begin
          (x₈ ≡⟨ (sym $ fromBinary∘toBinary{8} x₈) ⟩
          fromBinary (toBinary{8} x₈)
            ≡⟨ cong fromBinary
                 (Lemmas.toList-injective (toBinary{8} x₈) (Vec.fromList xs“)
                    (sym (proj₁ xs“×bits≡)))
            ⟩
          fromBinary (Vec.fromList xs“) ∎)))
        (∷-injectiveʳ ih))
    where
    open ≡-Reasoning
    module ≤ = Nat.≤-Reasoning

    xs = Vec.toList (toBinary{8} x₈)
    xs“ = x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ [ x₇ ]
    xs₂ = toBitRep bₕ (x₉ ∷ bₜ)

    xsLen : length xs ≡ 8
    xsLen = Lemmas.toListLength (toBinary{8} x₈)

    xs“×bits≡ : xs“ ≡ xs × bits ≡ xs₂
    xs“×bits≡ =
      Lemmas.length-++-≡ xs“ bits xs xs₂ bits≡
        (begin
          length xs“ ≡⟨⟩
          8 ≡⟨ sym xsLen ⟩
          length xs ∎)

    ih = serializeValueRaw≡ bits{bₜ = x₉ ∷ bₜ} bₕ<8 (proj₂ xs“×bits≡) u

serializeValue : Serializer BitStringValue
Singleton.x (serializeValue x) =
  let (bₕ , bₜ) = serializeValueRaw ∘ Singleton.x ∘ BitStringValue.bits $ x
  in bₕ ∷ bₜ
Singleton.x≡ (serializeValue (mkBitStringValue bₕ bₜ bₕ<8 (singleton bits bits≡) unusedBits refl)) =
  serializeValueRaw≡ bits bₕ<8 bits≡ unusedBits

serialize : Serializer BitString
serialize = TLV.serialize serializeValue
