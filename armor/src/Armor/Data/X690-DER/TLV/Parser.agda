open import Armor.Binary
open import Armor.Data.X690-DER.Length
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.TLV.Properties as TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parser
import      Armor.Grammar.Parallel
open import Armor.Prelude
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X690-DER.TLV.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

module parseTLV
  (t : UInt8) (tName : String) (A : @0 List UInt8 → Set)
  (p : ∀ n → Parser (Logging ∘ Dec) (ExactLength A n))
  where

  here' = "parseTLV: " String.++ tName

  open ≡-Reasoning

  parseTLV : Parser (Logging ∘ Dec) (TLV t A)
  runParser parseTLV [] = do
    tell $ here' String.++ ": underflow reading tag"
    return ∘ no $ λ where
      (success .(t ∷ l ++ v) read read≡ (mkTLV {l} {v} len val len≡ refl) suffix ())
  runParser parseTLV (x ∷ xs) = do
    case x ≟ t of λ where
      (no  x≢) → do
        tell $ here' String.++ ": tag mismatch, got " String.++ show (toℕ x)
        return ∘ no $ λ where
          (success .(t ∷ l ++ v) read read≡ (mkTLV{l}{v} len val len≡ refl) suffix ps≡) →
            contradiction (sym (∷-injectiveˡ ps≡)) x≢
      (yes refl) → do
        yes (success pre₀ r₀ r₀≡ len₀ suf₀ ps≡₀) ← runParser parseLen xs
          where no ¬parse → do
            tell $ here' String.++ ": underflow parsing length"
            return ∘ no $ λ where
              (success .(x ∷ l ++ v) read read≡ (mkTLV{l}{v} len val len≡ refl) suffix ps≡) → ‼
                contradiction
                  (success l (length l) refl len (v ++ suffix)
                    (∷-injectiveʳ (begin (x ∷ l ++ v ++ suffix  ≡⟨ cong (x ∷_) (solve (++-monoid UInt8)) ⟩
                                         x ∷ (l ++ v) ++ suffix ≡⟨ ps≡ ⟩
                                         x ∷ xs                 ∎))))
                  ¬parse
        yes (success pre₁ r₁ r₁≡ (mk×ₚ val (─ lenVal)) suf₁ ps≡₁) ← runParser (p (getLength len₀)) suf₀
          where no ¬parse → do
            tell $ here' String.++ ": error parsing value: " String.++ show (map toℕ (take 10 (suf₀)))
            return ∘ no $ λ where
              (success .(x ∷ l ++ v) read read≡ (mkTLV{l}{v} len val len≡ refl) suffix ps≡) → ‼
                let @0 xs≡ : pre₀ ++ suf₀ ≡ l ++ v ++ suffix
                    xs≡ = begin
                      pre₀ ++ suf₀       ≡⟨ ps≡₀ ⟩
                      xs                 ≡⟨ (sym $ ∷-injectiveʳ ps≡) ⟩
                      (l ++ v) ++ suffix ≡⟨ solve (++-monoid UInt8) ⟩
                      l ++ v ++ suffix   ∎

                    @0 pre₀≡ : pre₀ ≡ l
                    pre₀≡ = Length.nosubstrings xs≡ len₀ len

                    @0 len≡' : getLength len ≡ getLength len₀
                    len≡' = Length.unambiguous-getLength (sym pre₀≡) len len₀
                in
                contradiction
                  (success v _ refl
                    (mk×ₚ val (─ trans (sym len≡) len≡')) suffix
                    (++-cancelˡ pre₀
                      (begin (pre₀ ++ v ++ suffix ≡⟨ cong (λ x → x ++ v ++ suffix) pre₀≡ ⟩
                              l ++ v ++ suffix    ≡⟨ solve (++-monoid UInt8) ⟩
                              (l ++ v) ++ suffix  ≡⟨ ∷-injectiveʳ ps≡ ⟩
                              xs                  ≡⟨ sym ps≡₀ ⟩
                              pre₀ ++ suf₀        ∎))))
                  ¬parse
        return (yes
          (success
            (t ∷ pre₀ ++ pre₁) (1 + r₀ + r₁)
            (cong suc
              (begin (r₀ + r₁                   ≡⟨ cong (_+ r₁) r₀≡ ⟩
                      length pre₀ + r₁          ≡⟨ cong (length pre₀ +_) r₁≡ ⟩
                      length pre₀ + length pre₁ ≡⟨ (sym $ length-++ pre₀) ⟩
                      length (pre₀ ++ pre₁)     ∎)))
            (mkTLV len₀ val (sym lenVal) refl) suf₁
            (cong (x ∷_)
              (begin ((pre₀ ++ pre₁) ++ suf₁ ≡⟨ solve (++-monoid UInt8) ⟩
                      pre₀ ++ pre₁ ++ suf₁   ≡⟨ cong (pre₀ ++_) ps≡₁ ⟩
                      pre₀ ++ suf₀           ≡⟨ ps≡₀ ⟩
                      xs                      ∎)))))

open parseTLV public using (parseTLV)

parseTLVLenBound
  : ∀ {t A} l u → (tName : String) → Parser (Logging ∘ Dec) (TLV t A)
    → Parser (Logging ∘ Dec) (Σₚ (TLV t A) (TLVLenBounded l u))
runParser (parseTLVLenBound l u tName p) xs = do
  yes (success pre r r≡ v suf bs≡) ← runParser p xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success pre' r' r'≡ (mk×ₚ v' _) suf' bs≡') →
          contradiction (success pre' r' r'≡ v' suf' bs≡') ¬parse
  case inRange? l u (getLength (TLV.len v)) of λ where
    (yes l≤len≤u) →
      return (yes
        (success pre r r≡ (mk×ₚ v l≤len≤u) suf bs≡))
    (no  ¬l≤len≤u) → do
      tell $ "parseTLVLenBound: " String.++ tName String.++ ": given length bounds violated"
      return ∘ no $ λ where
        (success pre' r' r'≡ (mk×ₚ v' l≤len≤u) suf' bs≡') → ‼
          let @0 len≡ : getLength (TLV.len v) ≡ getLength (TLV.len v')
              len≡ = TLV.getLengthLen≡ (trans₀ bs≡ (sym bs≡')) v v'
          in
          contradiction (subst (InRange l u) (sym len≡) l≤len≤u) ¬l≤len≤u

parseTLVSizeBound
  : ∀ {t A} (size : ∀ {@0 bs} → A bs → ℕ) (uniqueSize : ∀ {@0 bs} → (a₁ a₂ : A bs) → size a₁ ≡ size a₂)
    → ∀ l u
    → (tName : String) → Parser (Logging ∘ Dec) (TLV t A)
    → Parser (Logging ∘ Dec) (Σₚ (TLV t A) (TLVSizeBounded size l u))
runParser (parseTLVSizeBound size uniqueSize l u tName p) xs = do
  yes (success pre r r≡ tlv@(mkTLV{v = v} len val len≡ bs≡) suf ps≡) ← runParser p xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success pre' r' r'≡ (mk×ₚ v' _refl) suf' bs≡') →
          contradiction (success pre' r' r'≡ v' suf' bs≡') ¬parse
  case inRange? l u (size val) of λ where
    (no ¬p) → do
      tell $
        "parseTLVSizeBound: " String.++ tName
        String.++ ": size " String.++ show (size val)
        String.++ " out of bounds: " String.++ show l String.++ "," String.++ show u
      return ∘ no $ λ where
        (success prefix read read≡ (mk×ₚ tlv'@(mkTLV{v = v'} len' val' len≡' bs≡') ir) suffix ps≡') →
          let
            xs≡ : Erased (prefix ++ suffix ≡ pre ++ suf)
            xs≡ = ─ trans ps≡' (sym ps≡)

            prefix≡ : Erased (prefix ≡ pre)
            prefix≡ = ─ TLV.nosubstrings (¡ xs≡) tlv' tlv

            v≡ : Erased (v ≡ v')
            v≡ = ─ TLV.valBS≡ (sym (¡ prefix≡)) tlv tlv' 

            len≡ : Erased (size val' ≡ size val)
            len≡ = ─
              (case (¡ v≡) ret (const _) of λ where
                refl → uniqueSize val' val)
          in
          contradiction (subst (InRange{B = ℕ} l u) (¡ len≡) ir) ¬p
    (yes p) →
      return (yes (success pre r r≡ (mk×ₚ tlv p) suf ps≡))
  where
  open ≡-Reasoning

parseTLVNonEmpty
  : ∀ {t A} → Parser (Logging ∘ Dec) (TLV t A)
    → Parser (Logging ∘ Dec) (Σₚ (TLV t A) TLVNonEmptyVal)
runParser (parseTLVNonEmpty p) xs = do
  yes (success pre r r≡ v suf bs≡) ← runParser p xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success pre' r' r'≡ (mk×ₚ v' _) suf' bs≡') →
          contradiction (success pre' r' r'≡ v' suf' bs≡') ¬parse
  case 1 ≤? (getLength (TLV.len v)) of λ where
    (yes l≤len≤u) →
      return (yes
        (success pre r r≡ (mk×ₚ v l≤len≤u) suf bs≡))
    (no  ¬l≤len≤u) → do
      tell $ "parseTLVLenBound" String.++ ": given length bounds violated"
      return ∘ no $ λ where
        (success pre' r' r'≡ (mk×ₚ v' l≤len≤u) suf' bs≡') → ‼
          let @0 len≡ : getLength (TLV.len v) ≡ getLength (TLV.len v')
              len≡ = TLV.getLengthLen≡ (trans₀ bs≡ (sym bs≡')) v v'
          in
          contradiction (subst (1 ≤_) (sym len≡) l≤len≤u) ¬l≤len≤u

