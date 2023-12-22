open import Armor.Binary
open import Armor.Data.X690-DER.BitString.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.TLV.Properties as TLV
import      Armor.Grammar.Definitions
open import Armor.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Armor.Data.X690-DER.BitString.Properties where

open Armor.Grammar.Definitions              UInt8
open ≡-Reasoning

uniqueUnusedBits : ∀ {bₕ bₜ} → Unique (UnusedBits bₕ bₜ)
uniqueUnusedBits {bₜ = []} x y = ≡-unique x y
uniqueUnusedBits {bₜ = x₁ ∷ []} x y = ≡-unique x y
uniqueUnusedBits {bₜ = x₁ ∷ x₂ ∷ bₜ} x y = uniqueUnusedBits{bₜ = x₂ ∷ bₜ} x y

unusedBits? : ∀ b bs → Dec (UnusedBits b bs)
unusedBits? b [] = toℕ b ≟ 0
unusedBits? b (x ∷ []) = drop (8 - toℕ b) (Vec.toList (toBinary{8} x)) ≟ replicate (toℕ b) #0
unusedBits? b (x ∷ x₁ ∷ bs) = unusedBits? b (x₁ ∷ bs)

private
  @0 toBitRep-injectiveWF
    : ∀ (@0 bₕ₁ bₕ₂ bₜ₁ bₜ₂)
      → Acc _<_ (length bₜ₁)
      → @0 toℕ bₕ₁ < 8 → @0 toℕ bₕ₂ < 8
      → @0 UnusedBits bₕ₁ bₜ₁ → @0 UnusedBits bₕ₂ bₜ₂
      → toBitRep bₕ₁ bₜ₁ ≡ toBitRep bₕ₂ bₜ₂ → (bₕ₁ ,′ bₜ₁) ≡ (bₕ₂ ,′ bₜ₂)
  toBitRep-injectiveWF bₕ₁ bₕ₂ [] [] ac bₕ₁<8 bₕ₂<8 u₁ u₂ rep≡
    rewrite Fin.toℕ-injective{i = bₕ₁}{bₕ₂} (trans u₁ (sym u₂)) = refl
  toBitRep-injectiveWF bₕ₁ bₕ₂ [] (b₂ ∷ []) ac bₕ₁<8 bₕ₂<8 u₁ u₂ rep≡ =
    contradiction{P = length xs ≡ 0}
      (cong length (sym rep≡))
      (>⇒≢ takeLen₄)
    where
    len₂ : length (Vec.toList (toBinary{8} b₂)) ≡ 8
    len₂ = Lemmas.toListLength (toBinary b₂)
  
    xs = take (8 - toℕ bₕ₂) (Vec.toList (toBinary{8} b₂))
  
    takeLen₂ : length xs ≡ (8 - toℕ bₕ₂) ⊓ 8
    takeLen₂ = trans (length-take (8 - toℕ bₕ₂) (Vec.toList (toBinary{8} b₂)))
                 (cong ((8 - toℕ bₕ₂) ⊓_) len₂)
  
    takeLen₃ : length xs ≡ 8 - toℕ bₕ₂
    takeLen₃ = trans takeLen₂ (m≤n⇒m⊓n≡m (m∸n≤m 8 (toℕ bₕ₂)))
  
    takeLen₄ : length xs > 0
    takeLen₄ = ≤-trans (0 < 8 - toℕ bₕ₂ ∋ m<n⇒0<n∸m bₕ₂<8) (Lemmas.≡⇒≤ (sym takeLen₃))
  toBitRep-injectiveWF bₕ₁ bₕ₂ [] (b₂₁ ∷ b₂₂ ∷ bₜ₂) ac bₕ₁<8 bₕ₂<8 u₁ u₂ rep≡ =
    contradiction{P = 0 ≥ 8} (≤-trans len≥ (Lemmas.≡⇒≤ (sym (cong length rep≡)))) λ ()
    where
    module ≤ = ≤-Reasoning
  
    xs = Vec.toList (toBinary{8} b₂₁) ++ toBitRep bₕ₂ (b₂₂ ∷ bₜ₂)
  
    len≥ : length xs ≥ 8
    len≥ = ≤.begin
      8 ≤.≡⟨ (sym $ Lemmas.toListLength (toBinary{8} b₂₁)) ⟩
      length (Vec.toList $ toBinary{8} b₂₁) ≤.≤⟨ m≤m+n _ _ ⟩
      length (Vec.toList $ toBinary{8} b₂₁) + length (toBitRep bₕ₂ (b₂₂ ∷ bₜ₂))
        ≤.≡⟨ sym (length-++ (Vec.toList (toBinary{8} b₂₁)) {ys = toBitRep bₕ₂ (b₂₂ ∷ bₜ₂)}) ⟩
      length (Vec.toList (toBinary{8} b₂₁) ++ toBitRep bₕ₂ (b₂₂ ∷ bₜ₂)) ≤.≡⟨⟩
      length xs ≤.∎
      -- length (Vec.toList $ toBinary{8} b₂₁) + length (toBitRep bₕ₂ (b₂₂ ∷ bₜ₂)) ≤.≡⟨ sym (length-++ (Vec.toList $ toBinary{8} b₂₁)) ⟩
      -- length (Vec.toList (toBinary{8} b₂₁) ++ toBitRep bₕ₂ (b₂₂ ∷ bₜ₂)) ≤.≡⟨⟩
      -- (length xs ≤.∎)
  toBitRep-injectiveWF bₕ₁ bₕ₂ (x ∷ []) [] ac bₕ₁<8 bₕ₂<8 u₁ u₂ rep≡ =
    contradiction{P = length xs ≡ 0}
      (cong length rep≡)
      (>⇒≢ takeLen₄)
    where
    len₂ : length (Vec.toList (toBinary{8} x)) ≡ 8
    len₂ = Lemmas.toListLength (toBinary x)
  
    xs = take (8 - toℕ bₕ₁) (Vec.toList (toBinary{8} x))
  
    takeLen₂ : length xs ≡ (8 - toℕ bₕ₁) ⊓ 8
    takeLen₂ = trans (length-take (8 - toℕ bₕ₁) (Vec.toList (toBinary{8} x)))
                 (cong ((8 - toℕ bₕ₁) ⊓_) len₂)
  
    takeLen₃ : length xs ≡ 8 - toℕ bₕ₁
    takeLen₃ = trans takeLen₂ (m≤n⇒m⊓n≡m (m∸n≤m 8 (toℕ bₕ₁)))
  
    takeLen₄ : length xs > 0
    takeLen₄ = ≤-trans (0 < 8 - toℕ bₕ₁ ∋ m<n⇒0<n∸m bₕ₁<8) (Lemmas.≡⇒≤ (sym takeLen₃))
  
  toBitRep-injectiveWF bₕ₁ bₕ₂ (x ∷ []) (x₁ ∷ []) ac bₕ₁<8 bₕ₂<8 u₁ u₂ rep≡ =
    ‼ (cong₂ _,′_ bₕ≡
        (cong (_∷ [])
          (toBinary-injective x x₁
            (Lemmas.toList-injective (toBinary{8} x) (toBinary{8} x₁) xs'≡))))
    where
    xs₁' = Vec.toList (toBinary{8} x)
    xs₂' = Vec.toList (toBinary{8} x₁)
  
    len₁ : length xs₁' ≡ 8
    len₁ = Lemmas.toListLength (toBinary x)
  
    len₂ : length xs₂' ≡ 8
    len₂ = Lemmas.toListLength (toBinary x₁)
  
    xs₁ = take (8 ∸ Fin.toℕ bₕ₁) xs₁'
    xs₂ = take (8 ∸ Fin.toℕ bₕ₂) xs₂'
  
    len₁≡ : length xs₁ ≡ 8 - toℕ bₕ₁
    len₁≡ = begin
      (length xs₁ ≡⟨ length-take (8 - toℕ bₕ₁) xs₁' ⟩
      (8 - toℕ bₕ₁) ⊓ length xs₁' ≡⟨ cong ((8 ∸ toℕ bₕ₁) ⊓_) len₁ ⟩
      (8 - toℕ bₕ₁) ⊓ 8 ≡⟨ m≤n⇒m⊓n≡m (m∸n≤m 8 (toℕ bₕ₁)) ⟩
      8 - toℕ bₕ₁ ∎)
  
    len₂≡ : length xs₂ ≡ 8 - toℕ bₕ₂
    len₂≡ = begin
      (length xs₂ ≡⟨ length-take (8 - toℕ bₕ₂) xs₂' ⟩
      (8 - toℕ bₕ₂) ⊓ length xs₂' ≡⟨ cong ((8 ∸ toℕ bₕ₂) ⊓_) len₂ ⟩
      (8 - toℕ bₕ₂) ⊓ 8 ≡⟨ m≤n⇒m⊓n≡m (m∸n≤m 8 (toℕ bₕ₂)) ⟩
      8 - toℕ bₕ₂ ∎)
  
    8-≡ : 8 - toℕ bₕ₁ ≡ 8 - toℕ bₕ₂
    8-≡ = trans (sym len₁≡) (trans (‼ cong length rep≡) len₂≡)
  
    @0 bₕ≡ : bₕ₁ ≡ bₕ₂
    bₕ≡ =
      Fin.toℕ-injective
        (∸-cancelˡ-≡ (<⇒≤ bₕ₁<8) (<⇒≤ bₕ₂<8) 8-≡)
  
    @0 xs'≡ : xs₁' ≡ xs₂'
    xs'≡ = begin
      xs₁' ≡⟨ (sym $ take++drop (8 - toℕ bₕ₁) xs₁') ⟩
      xs₁ ++ drop (8 - toℕ bₕ₁) xs₁' ≡⟨ cong (_++ (drop (8 - toℕ bₕ₁) xs₁')) rep≡ ⟩
      xs₂ ++ drop (8 - toℕ bₕ₁) xs₁' ≡⟨ cong (xs₂ ++_) u₁ ⟩
      xs₂ ++ replicate (toℕ bₕ₁) #0 ≡⟨ cong (λ x → xs₂ ++ replicate x #0) (cong toℕ bₕ≡) ⟩
      xs₂ ++ replicate (toℕ bₕ₂) #0 ≡⟨ cong (xs₂ ++_) (sym u₂) ⟩
      xs₂ ++ drop (8 - toℕ bₕ₂) xs₂' ≡⟨ take++drop (8 - toℕ bₕ₂) xs₂' ⟩
      xs₂' ∎
  
  toBitRep-injectiveWF bₕ₁ bₕ₂ (x ∷ []) (x₁ ∷ x₂ ∷ []) ac bₕ₁<8 bₕ₂<8 u₁ u₂ rep≡ =
    contradiction{P = length xs₁ ≤ 8}
      xs₁Len
      (<⇒≱ (≤.begin (9 ≤.≤⟨ xs₂Len ⟩
                    length (xs₂₁ ++ xs₂₂) ≤.≡⟨ cong length (sym rep≡) ⟩
                    length xs₁ ≤.∎)))
    where
    module ≤ = ≤-Reasoning
  
    xs₁' = Vec.toList (toBinary{8} x)
    xs₁  = take (8 ∸ Fin.toℕ bₕ₁) xs₁'
  
    xs₁Len : length xs₁ ≤ 8
    xs₁Len = ≤.begin
      length xs₁ ≤.≡⟨ length-take (8 - toℕ bₕ₁) _ ⟩
      (8 - toℕ bₕ₁) ⊓ length xs₁' ≤.≡⟨ cong ((8 ∸ toℕ bₕ₁) ⊓_) (Lemmas.toListLength (toBinary{8} x)) ⟩
      (8 - toℕ bₕ₁) ⊓ 8 ≤.≡⟨ m≤n⇒m⊓n≡m (m∸n≤m _ (toℕ bₕ₁)) ⟩
      8 - toℕ bₕ₁ ≤.≤⟨ m∸n≤m _ (toℕ bₕ₁) ⟩
      8 ≤.∎
  
    xs₂₁  = Vec.toList (toBinary{8} x₁)
  
    xs₂₂' = Vec.toList (toBinary{8} x₂)
    xs₂₂  = take (8 - toℕ bₕ₂) xs₂₂'
  
    xs₂₂Len : length xs₂₂ > 0
    xs₂₂Len = ≤.begin
      (1 ≤.≤⟨ m<n⇒0<n∸m bₕ₂<8 ⟩
      8 - toℕ bₕ₂ ≤.≡⟨ sym (m≤n⇒m⊓n≡m (m∸n≤m 8 (toℕ bₕ₂))) ⟩
      (8 - toℕ bₕ₂) ⊓ 8 ≤.≡⟨ cong ((8 ∸ toℕ bₕ₂) ⊓_) (sym $ Lemmas.toListLength (toBinary{8} x₂)) ⟩
      (8 - toℕ bₕ₂) ⊓ length xs₂₂' ≤.≡⟨ sym (length-take (8 ∸ toℕ bₕ₂) _) ⟩
      length xs₂₂ ≤.∎)
  
    xs₂Len : length (xs₂₁ ++ xs₂₂) > 8
    xs₂Len = ≤.begin
      8 + 1 ≤.≡⟨ cong (_+ 1) (sym (Lemmas.toListLength (toBinary{8} x₁))) ⟩
      length xs₂₁ + 1 ≤.≤⟨ +-monoʳ-≤ (length xs₂₁) xs₂₂Len ⟩
      length xs₂₁ + length xs₂₂ ≤.≡⟨ sym (length-++ xs₂₁ {xs₂₂}) ⟩
      length (xs₂₁ ++ xs₂₂) ≤.∎
  toBitRep-injectiveWF bₕ₁ bₕ₂ (x ∷ []) (x₁ ∷ x₂ ∷ x₃ ∷ bₜ₂) ac bₕ₁<8 bₕ₂<8 u₁ u₂ rep≡ =
    contradiction{P = length xs₁ ≤ 8}
      xs₁Len
      (<⇒≱ (≤.begin
        (9 ≤.≤⟨ xs₂Len ⟩
        length (xs₂₁ ++ xs₂₂ ++ xs₂₃) ≤.≡⟨ cong length (sym rep≡) ⟩
        length xs₁ ≤.∎)))
    where
    module ≤ = ≤-Reasoning
  
    xs₁' = Vec.toList (toBinary{8} x)
    xs₁  = take (8 ∸ Fin.toℕ bₕ₁) xs₁'
  
    xs₁Len : length xs₁ ≤ 8
    xs₁Len = ≤.begin
      length xs₁ ≤.≡⟨ length-take (8 - toℕ bₕ₁) _ ⟩
      (8 - toℕ bₕ₁) ⊓ length xs₁' ≤.≡⟨ cong ((8 ∸ toℕ bₕ₁) ⊓_) (Lemmas.toListLength (toBinary{8} x)) ⟩
      (8 - toℕ bₕ₁) ⊓ 8 ≤.≡⟨ m≤n⇒m⊓n≡m (m∸n≤m _ (toℕ bₕ₁)) ⟩
      8 - toℕ bₕ₁ ≤.≤⟨ m∸n≤m _ (toℕ bₕ₁) ⟩
      8 ≤.∎
  
    xs₂₁ = Vec.toList (toBinary{8} x₁)
    xs₂₂ = Vec.toList (toBinary{8} x₂)
    xs₂₃ = toBitRep bₕ₂ (x₃ ∷ bₜ₂)
  
    xs₂Len : length (xs₂₁ ++ xs₂₂ ++ xs₂₃) > 8
    xs₂Len = ≤.begin
      8 + 1 ≤.≤⟨ toWitness{Q = _ ≤? _} tt ⟩
      8 + 8 ≤.≡⟨ cong₂ _+_ (sym $ Lemmas.toListLength (toBinary{8} x₁)) (sym $ Lemmas.toListLength (toBinary{8} x₂)) ⟩
      length xs₂₁ + length xs₂₂ ≤.≡⟨ sym (length-++ xs₂₁ {xs₂₂}) ⟩
      length (xs₂₁ ++ xs₂₂) ≤.≤⟨ m≤m+n (length (xs₂₁ ++ xs₂₂)) _ ⟩
      length (xs₂₁ ++ xs₂₂) + length xs₂₃ ≤.≡⟨ sym (length-++ (xs₂₁ ++ xs₂₂) {xs₂₃}) ⟩
      length ((xs₂₁ ++ xs₂₂) ++ xs₂₃) ≤.≡⟨ cong length (++-assoc xs₂₁ xs₂₂ xs₂₃) ⟩
      length (xs₂₁ ++ xs₂₂ ++ xs₂₃) ≤.∎
  
  toBitRep-injectiveWF bₕ₁ bₕ₂ bₜ₁''@(x ∷ bₜ₁'@(x₁ ∷ bₜ₁)) bₜ₂ ac = help bₜ₂ ac
    where
    module ≤ = ≤-Reasoning
  
    toBitRepLen : ∀ bₜ → (toℕ bₕ₁ < 8) → length (toBitRep bₕ₁ (x₁ ∷ bₜ)) > 0
    toBitRepLen [] bₕ₁<8 = xsLen
      where
      xs' = Vec.toList (toBinary{8} x₁)
      xs  = take (8 - toℕ bₕ₁) xs'
  
      xsLen : length xs > 0
      xsLen = ≤.begin
        (1 ≤.≤⟨ m<n⇒0<n∸m bₕ₁<8 ⟩
        8 - toℕ bₕ₁ ≤.≡⟨ sym (m≤n⇒m⊓n≡m (m∸n≤m 8 (toℕ bₕ₁))) ⟩
        (8 - toℕ bₕ₁) ⊓ 8 ≤.≡⟨ cong ((8 ∸ toℕ bₕ₁) ⊓_) (sym $ Lemmas.toListLength (toBinary{8} x₁)) ⟩
        (8 - toℕ bₕ₁) ⊓ length xs' ≤.≡⟨ sym (length-take (8 ∸ toℕ bₕ₁) _) ⟩
        length xs ≤.∎)
  
    toBitRepLen (x ∷ bₜ) bₕ₁<8 =
      ≤.begin
        1 ≤.≤⟨ toWitness{Q = _ ≤? _} tt ⟩
        8 ≤.≡⟨ sym xsLen ⟩
        length xs ≤.≤⟨ m≤m+n (length xs) (length (toBitRep bₕ₁ (x ∷ bₜ))) ⟩
        length xs + length (toBitRep bₕ₁ (x ∷ bₜ)) ≤.≡⟨ sym (length-++ xs {toBitRep bₕ₁ (x ∷ bₜ)}) ⟩
        length (xs ++ toBitRep bₕ₁ (x ∷ bₜ)) ≤.∎
      where
      xs = Vec.toList (toBinary{8} x₁)
  
      xsLen : length xs ≡ 8
      xsLen = Lemmas.toListLength (toBinary{8} x₁)
  
    help : (@0 bₜ₂ : List UInt8)
           → Acc _<_ (length bₜ₁'')
           → @0 Fin.toℕ bₕ₁ < 8 → @0 Fin.toℕ bₕ₂ < 8
           → @0 UnusedBits bₕ₁ (x₁ ∷ bₜ₁) → @0 UnusedBits bₕ₂ bₜ₂
           → Vec.toList (toBinary{8} x) ++ toBitRep bₕ₁ (x₁ ∷ bₜ₁) ≡ toBitRep bₕ₂ bₜ₂
           → (bₕ₁ ,′ x ∷ x₁ ∷ bₜ₁) ≡ (bₕ₂ ,′ bₜ₂)
    help [] ac bₕ₁<8 bₕ₂<8 u₁ u₂ rep≡ =
      contradiction{P = 8 ≡ 0}
        (begin (8 ≡⟨ (sym $ Lemmas.toListLength (toBinary{8} x)) ⟩
               length xs ≡⟨ cong length (++-conicalˡ xs _ rep≡) ⟩
               length{A = Bool} [] ≡⟨⟩
               0 ∎))
        λ ()
      where
      xs = Vec.toList (toBinary{8} x)
    help (x' ∷ []) ac bₕ₁<8 bₕ₂<8 u₁ u₂ rep≡ =
      contradiction{P = length xs₁ ≤ 8}
        xs₁Len
        (<⇒≱ (≤.begin
          9 ≤.≤⟨ xs₂Len ⟩
          length (xs₂₁ ++ xs₂₂) ≤.≡⟨ sym $ cong length (sym rep≡) ⟩
          length xs₁ ≤.∎))
      where
      xs₁' = Vec.toList (toBinary{8} x')
      xs₁  = take (8 - toℕ bₕ₂) xs₁'
  
      xs₁Len : length xs₁ ≤ 8
      xs₁Len = ≤.begin
        length xs₁ ≤.≡⟨ length-take (8 - toℕ bₕ₂) _ ⟩
        (8 - toℕ bₕ₂) ⊓ length xs₁' ≤.≡⟨ cong ((8 ∸ toℕ bₕ₂) ⊓_) (Lemmas.toListLength (toBinary{8} x')) ⟩
        (8 - toℕ bₕ₂) ⊓ 8 ≤.≡⟨ m≤n⇒m⊓n≡m (m∸n≤m _ (toℕ bₕ₂)) ⟩
        8 - toℕ bₕ₂ ≤.≤⟨ m∸n≤m _ (toℕ bₕ₂) ⟩
        8 ≤.∎
  
      xs₂₁ = Vec.toList (toBinary{8} x)
      xs₂₂ = toBitRep bₕ₁ (x₁ ∷ bₜ₁)
  
      xs₂Len : length (xs₂₁ ++ xs₂₂) > 8
      xs₂Len = ≤.begin
        (8 + 1 ≤.≡⟨ cong (_+ 1) (sym $ Lemmas.toListLength (toBinary{8} x)) ⟩
        length xs₂₁ + 1 ≤.≤⟨ +-monoʳ-≤ (length xs₂₁) (toBitRepLen bₜ₁ bₕ₁<8) ⟩
        length xs₂₁ + length xs₂₂ ≤.≡⟨ sym (length-++ xs₂₁ {xs₂₂}) ⟩
        length (xs₂₁ ++ xs₂₂) ≤.∎)
    help (x' ∷ x₁' ∷ bₜ₂) (WellFounded.acc rs) bₕ₁<8 bₕ₂<8 u₁ u₂ rep≡ =
      ‼ cong₂ _,′_ ih₁ (cong₂ _∷_ (toBinary-injective{n = 8} x x' (Lemmas.toList-injective _ _ xs≡)) ih₂)
        
      where
      xs₁ = Vec.toList (toBinary{8} x)
      xs₂ = Vec.toList (toBinary{8} x')
  
      xs₁Len : length xs₁ ≡ 8
      xs₁Len = Lemmas.toListLength (toBinary{8} x)
  
      xs₂Len : length xs₂ ≡ 8
      xs₂Len = Lemmas.toListLength (toBinary{8} x')
  
      rep≡' : toBitRep bₕ₁ (x₁ ∷ bₜ₁) ≡ toBitRep bₕ₂ (x₁' ∷ bₜ₂)
      rep≡' = begin
        (toBitRep bₕ₁ (x₁ ∷ bₜ₁) ≡⟨ sym (Lemmas.drop-length-++ xs₁ _) ⟩
        drop (length xs₁) (xs₁ ++ toBitRep bₕ₁ (x₁ ∷ bₜ₁)) ≡⟨ cong (drop (length xs₁)) rep≡ ⟩
        drop (length xs₁) (xs₂ ++ toBitRep bₕ₂ (x₁' ∷ bₜ₂)) ≡⟨ cong (λ x → drop x (xs₂ ++ toBitRep bₕ₂ (x₁' ∷ bₜ₂))) xs₁Len ⟩
        drop 8 (xs₂ ++ toBitRep bₕ₂ (x₁' ∷ bₜ₂)) ≡⟨ cong (λ x → drop x (xs₂ ++ toBitRep bₕ₂ (x₁' ∷ bₜ₂))) (sym xs₂Len) ⟩
        drop (length xs₂) (xs₂ ++ toBitRep bₕ₂ (x₁' ∷ bₜ₂)) ≡⟨ Lemmas.drop-length-++ xs₂ _ ⟩
        toBitRep bₕ₂ (x₁' ∷ bₜ₂) ∎)
  
      ih : (bₕ₁ ,′ (x₁ ∷ bₜ₁)) ≡ (bₕ₂ ,′ x₁' ∷ bₜ₂)
      ih = toBitRep-injectiveWF bₕ₁ bₕ₂ bₜ₁' (x₁' ∷ bₜ₂) (rs (length bₜ₁') ≤-refl) bₕ₁<8 bₕ₂<8 u₁ u₂ rep≡'
  
      ih₁ = cong proj₁ ih
      ih₂ = cong proj₂ ih
  
      xs≡ : xs₁ ≡ xs₂
      xs≡ = proj₁ (Lemmas.length-++-≡ xs₁ _ _ _ rep≡ (trans xs₁Len (sym xs₂Len)))
  
  
@0 toBitRep-injective
  : ∀ (@0 bₕ₁ bₕ₂ bₜ₁ bₜ₂)
    → @0 toℕ bₕ₁ < 8 → @0 toℕ bₕ₂ < 8
    → @0 UnusedBits bₕ₁ bₜ₁ → @0 UnusedBits bₕ₂ bₜ₂
    → toBitRep bₕ₁ bₜ₁ ≡ toBitRep bₕ₂ bₜ₂ → (bₕ₁ ,′ bₜ₁) ≡ (bₕ₂ ,′ bₜ₂)
toBitRep-injective bₕ₁ bₕ₂ bₜ₁ bₜ₂ = toBitRep-injectiveWF bₕ₁ bₕ₂ bₜ₁ bₜ₂ (Nat.<-wellFounded _)
  where
  import Data.Nat.Induction
  module Nat = Data.Nat.Induction

instance
  eq : Eq (Exists─ (List UInt8) BitStringValue)
  Eq._≟_ eq (─ bs₁ , mkBitStringValue bₕ₁ bₜ₁ bₕ₁<8 (singleton bits₁ bits₁≡) unusedBits₁ bs≡₁) (─ bs₂ , mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 (singleton bits₂ bits₂≡) unusedBits₂ bs≡₂) =
    case bits₁ ≟ bits₂ ret (const _) of λ where
      (no ¬p) → no λ where refl → contradiction refl ¬p
      (yes bits≡) →
        let @0 bₕₜ≡ : Erased _
            bₕₜ≡ = ─ toBitRep-injective bₕ₁ bₕ₂ bₜ₁ bₜ₂ bₕ₁<8 bₕ₂<8 unusedBits₁ unusedBits₂ (trans (sym bits₁≡) (trans bits≡ bits₂≡))

            @0 bₕ≡ : Erased (bₕ₁ ≡ bₕ₂)
            bₕ≡ = ─ cong proj₁ (Erased.x bₕₜ≡)

            @0 bₜ≡ : Erased (bₜ₁ ≡ bₜ₂)
            bₜ≡ = ─ cong proj₂ (Erased.x bₕₜ≡)

            @0 bs≡₁' : Erased (bs₁ ≡ bs₂)
            bs≡₁' = ─ (trans bs≡₁ (trans (cong₂ _∷_ (¡ bₕ≡) (¡ bₜ≡)) (sym bs≡₂)))
        in
        yes (begin (─ bs₁ , mkBitStringValue bₕ₁ bₜ₁ bₕ₁<8 (singleton bits₁ bits₁≡) unusedBits₁ bs≡₁
                     ≡⟨ ‼ subst₂
                          (λ h t →
                             (@0 h<8 : toℕ h < 8) (s : Singleton (toBitRep h t)) (@0 u : UnusedBits h t) (@0 eq₁ : bs₁ ≡ h ∷ t) →
                               _,e_{A = Erased (List UInt8)}{B = λ x → BitStringValue (Erased.x x)}
                                   (─ bs₁)
                                   (mkBitStringValue h t h<8 s u eq₁)
                             ≡ (─ bs₁ ,e mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 (singleton bits₂ bits₂≡) unusedBits₂ (trans (¡ bs≡₁') bs≡₂)))
                          (sym (¡ bₕ≡)) (sym (¡ bₜ≡))
                          (λ h<8 s u eq₁ →
                            let <8≡ : Erased (h<8 ≡ bₕ₂<8)
                                <8≡ = ─ ≤-unique _ _

                                s≡ : s ≡ singleton bits₂ bits₂≡
                                s≡ = uniqueSingleton _ _

                                u≡ : Erased (u ≡ unusedBits₂)
                                u≡ = ─ (uniqueUnusedBits{bₕ₂}{bₜ₂} u unusedBits₂)
                            in
                            subst₂
                              (λ x y → (─ bs₁ ,e mkBitStringValue bₕ₂ bₜ₂ x y u eq₁) ≡ (─ bs₁ ,e mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 (singleton bits₂ bits₂≡) unusedBits₂ _))
                              (sym (¡ <8≡)) (sym s≡)
                              (subst₂
                                (λ x y → (─ bs₁ ,e mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 (singleton bits₂ bits₂≡) x y) ≡ (─ bs₁ ,e mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 (singleton bits₂ bits₂≡) unusedBits₂ _) )
                                (sym (¡ u≡))
                                (≡-unique _ eq₁)
                                refl)
                            )
                          bₕ₁<8 (singleton bits₁ bits₁≡) unusedBits₁ bs≡₁ ⟩
                   ─ bs₁ ,e mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 (singleton bits₂ bits₂≡) unusedBits₂ (trans (¡ bs≡₁') bs≡₂)
                     ≡⟨ ‼ (subst
                             (λ bs → (@0 eq : bs ≡ bₕ₂ ∷ bₜ₂)
                                     → (─ bs ,e mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 (singleton bits₂ bits₂≡) unusedBits₂ eq)
                                       ≡ (─ bs₂ ,e mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 (singleton bits₂ bits₂≡) unusedBits₂ bs≡₂) )
                             (sym (¡ bs≡₁'))
                             (λ eq₁ →
                               cong (λ eq₁' → (─ bs₂ ,e mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 (singleton bits₂ bits₂≡) unusedBits₂ eq₁')) (≡-unique eq₁ _))
                             (trans (¡ bs≡₁') bs≡₂)) ⟩
                   ─ bs₂ ,e mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 (singleton bits₂ bits₂≡) unusedBits₂ bs≡₂ ∎))
    where
    open ≡-Reasoning

  eq≋ : Eq≋ BitStringValue
  eq≋ = Eq⇒Eq≋ it

@0 unambiguousValue : Unambiguous BitStringValue
unambiguousValue (mkBitStringValue bₕ₁ bₜ₁ bₕ₁<8 bits₁ unusedBits₁ bs≡₁) (mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 bits₂ unusedBits₂ bs≡₂) =
  ≡-elim (λ {bₕ₂} bₕ≡ → ∀ bₕ₂<8 bits₂ unusedBits₂ bs≡₂ → mkBitStringValue bₕ₁ bₜ₁ bₕ₁<8 bits₁ unusedBits₁ bs≡₁ ≡ mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 bits₂ unusedBits₂ bs≡₂)
    (λ bₕ₂<8 bits₂ unusedBits₂ bs≡₂' →
      ≡-elim (λ {bₜ₂} bₜ≡ → ∀ (bits₂ : Singleton (toBitRep bₕ₁ bₜ₂)) unusedBits₂ bs≡₂ → mkBitStringValue bₕ₁ bₜ₁ bₕ₁<8 bits₁ unusedBits₁ bs≡₁ ≡ mkBitStringValue bₕ₁ bₜ₂ bₕ₂<8 bits₂ unusedBits₂ bs≡₂)
        (λ bits₂ unusedBits₂ bs≡₂' →
          subst₂ (λ bits bs≡ → _ ≡ mkBitStringValue bₕ₁ bₜ₁ _ bits _ bs≡) (uniqueSingleton bits₁ bits₂) (≡-unique bs≡₁ bs≡₂')
            (subst₂ (λ x y → _ ≡ mkBitStringValue bₕ₁ bₜ₁ x _ y _) (≤-irrelevant bₕ₁<8 bₕ₂<8) (uniqueUnusedBits{bₜ = bₜ₁} unusedBits₁ unusedBits₂)
              refl))
        bₜ≡ bits₂ unusedBits₂ bs≡₂')
    bₕ≡ bₕ₂<8 bits₂ unusedBits₂ bs≡₂
  where
  @0 bs≡ : bₕ₁ ∷ bₜ₁ ≡ bₕ₂ ∷ bₜ₂
  bs≡ = trans₀ (sym bs≡₁) bs≡₂

  @0 bₕ≡ : bₕ₁ ≡ bₕ₂
  bₕ≡ = ∷-injectiveˡ bs≡

  @0 bₜ≡ : _
  bₜ≡ = ∷-injectiveʳ bs≡

@0 unambiguous : Unambiguous BitString
unambiguous = TLV.unambiguous unambiguousValue

@0 nonmalleableValue : NonMalleable RawBitStringValue
nonmalleableValue{bs₁ = .(bₕ ∷ bₜ)}{bs₂ = .(bₕ₁ ∷ bₜ₁)} str₁@(mkBitStringValue bₕ bₜ bₕ<8 (singleton bits bits≡) unusedBits refl) str₂@(mkBitStringValue bₕ₁ bₜ₁ bₕ<9 (singleton .bits bits≡₁) unusedBits₁ refl) refl =
  case
    toBitRep-injective bₕ bₕ₁ bₜ bₜ₁ bₕ<8 bₕ<9
      unusedBits unusedBits₁
      (trans (sym bits≡) bits≡₁)
  ret (const _) of λ where
    refl → case (‼ unambiguousValue str₁ str₂) ret (const _) of λ where
      refl → refl

@0 nonmalleable : NonMalleable RawBitString
nonmalleable = TLV.nonmalleable nonmalleableValue
