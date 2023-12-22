open import Armor.Binary
open import Armor.Data.X690-DER.Default.Properties
open import Armor.Data.X690-DER.Default.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X690-DER.Default.Parser  where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Seq         UInt8

module _ {A : @0 List UInt8 → Set} ⦃ eq≋ : Eq≋ A ⦄ {@0 bs' : List UInt8} (default : A bs') (loc : String) where
  -- parse : Unambiguous A → NoSubstrings A → Parser (Logging ∘ Dec) A → Parser (Logging ∘ Dec) (Default A default)
  -- runParser (parse ua ns p) xs = do
  --   yes x ← runParser 
  --   {!!}

  -- parse₁&₁≤
  --   : ∀ {@ 0 B : @0 List UInt8 → Set} n → Parser (Logging ∘ Dec) A → Parser (Logging ∘ Dec) B
  --     → @0 NoSubstrings A → @0 Unambiguous A → @0 NoSubstrings B → @0 NoConfusion A B
  --     → Parser (Logging ∘ Dec) (Length≤ (&ₚ (Default A default) B) n)
  -- runParser (parse₁&₁≤ n p₁ p₂ nn₁ ua₁ nn₂ nc) xs = do
  --   (yes (success pre₁ r₁ r₁≡ (mk×ₚ (mk&ₚ{pre₁₁}{pre₁₂} v₁₁ v₁₂ refl) v₁Len) suf₁ ps≡₁))
  --     ← runParser (Option.parseOption₁&₁≤ p₁ p₂ nn₁ nn₂ nc (tell $ loc String.++ ": length overflow") n) xs
  --     where no ¬parse → do
  --       tell $ loc String.++ ": failed to parse [default]"
  --       return ∘ no $ λ where
  --         (success prefix read read≡ (mk×ₚ (mk&ₚ v₁₁ v₁₂ refl) v₁Len) suffix ps≡) →
  --           contradiction
  --             (success prefix read read≡ (mk×ₚ (mk&ₚ (Default.value v₁₁) v₁₂ refl) v₁Len) suffix ps≡)
  --             ¬parse
  --   case (singleton v₁₁ refl) ret (const _) of λ where
  --     (singleton none refl) →
  --       return (yes
  --         (success pre₁ r₁ r₁≡ (mk×ₚ (mk&ₚ (mkDefault none tt) v₁₂ refl) v₁Len) suf₁ ps≡₁))
  --     (singleton (some v₁₁') refl) → case (_≋?_{A = A} v₁₁' default) ret (const _) of λ where
  --       (no ¬p) → return (yes
  --         (success pre₁ r₁ r₁≡
  --           (mk×ₚ (mk&ₚ (mkDefault (some v₁₁') (fromWitnessFalse{Q = _ ≋? _} ¬p)) v₁₂ refl) v₁Len)
  --           _ ps≡₁))
  --       (yes p) → do
  --         tell $ loc String.++ ": default value present!"
  --         return ∘ no $ λ where
  --           (success prefix read read≡ (mk×ₚ (mk&ₚ{prefix₁}{prefix₂} (mkDefault none notDefault) value₂ refl) valueLen) suffix ps≡) →
  --             let
  --               @0 ++≡ : pre₁₁ ++ (pre₁₂ ++ suf₁) ≡ prefix ++ suffix
  --               ++≡ = begin
  --                 pre₁₁ ++ (pre₁₂ ++ suf₁) ≡⟨ sym (++-assoc pre₁₁ pre₁₂ suf₁) ⟩
  --                 (pre₁₁ ++ pre₁₂) ++ suf₁ ≡⟨ ps≡₁ ⟩
  --                 xs ≡⟨ sym ps≡ ⟩
  --                 prefix ++ suffix ∎
  --             in
  --             contradiction
  --               value₂
  --               (nc ++≡ v₁₁')
  --           (success prefix read read≡ (mk×ₚ (mk&ₚ{prefix₁}{prefix₂} (mkDefault (some value₁) notDefault) value₂ refl) valueLen) suffix ps≡) →
  --             let
  --               @0 ++≡ : prefix₁ ++ prefix₂ ++ suffix ≡ pre₁₁ ++ pre₁₂ ++ suf₁
  --               ++≡ = begin
  --                 prefix₁ ++ prefix₂ ++ suffix ≡⟨ sym (++-assoc prefix₁ prefix₂ suffix) ⟩
  --                 (prefix₁ ++ prefix₂) ++ suffix ≡⟨ ps≡ ⟩
  --                 xs ≡⟨ sym ps≡₁ ⟩
  --                 (pre₁₁ ++ pre₁₂) ++ suf₁ ≡⟨ ++-assoc pre₁₁ pre₁₂ suf₁ ⟩
  --                 pre₁₁ ++ pre₁₂ ++ suf₁ ∎

  --               @0 prefix₁≡ : prefix₁ ≡ pre₁₁
  --               prefix₁≡ = nn₁ ++≡ value₁ v₁₁'

  --               @0 value₁≋ : value₁ ≋ v₁₁'
  --               value₁≋ = mk≋ prefix₁≡ (case prefix₁≡ ret (λ x → subst A x value₁ ≡ v₁₁') of λ where
  --                 refl → ‼ ua₁ value₁ v₁₁')
  --             in
  --             contradiction
  --               (trans≋ value₁≋ p)
  --               (toWitnessFalse notDefault)
  --   where
  --   open ≡-Reasoning
