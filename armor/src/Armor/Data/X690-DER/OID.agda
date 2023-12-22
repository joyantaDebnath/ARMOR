open import Armor.Binary
import      Armor.Data.X690-DER.OID.TCB as TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X690-DER.OID where

open Armor.Grammar.Parser UInt8

module OID where
  open TCB public
  open import Armor.Data.X690-DER.OID.Serializer public
  open import Armor.Data.X690-DER.OID.Properties public

open TCB public hiding
  (LeastBytes; leastBytes?; leastBytesUnique)

open import Armor.Data.X690-DER.OID.Parser public

mkOIDSubₛ
  : (lₚ : List UInt8) (lₑ : UInt8)
    → {@0 _ : True (All.all? ((_≥? 128) ∘ toℕ) lₚ)} {@0 _ : True (OID.leastBytes? lₚ)} {@0 _ : True (lₑ Fin.<? # 128)}
    → OIDSub (lₚ ∷ʳ lₑ)
mkOIDSubₛ lₚ lₑ {lₚ≥128}{leastDigs}{lₑ<128} = mkOIDSub lₚ (toWitness lₚ≥128) lₑ (toWitness lₑ<128) (toWitness leastDigs) refl

isOID? : Decidable (λ xs → OID xs)
isOID? xs =
  case Logging.val $ runParser parseOID xs of λ where
    (no ¬p) → no (λ o → contradiction (success _ _ refl o [] (++-identityʳ _)) ¬p)
    (yes (success prefix read read≡ value [] ps≡)) →
      yes (subst₀! OID (trans₀ (sym (++-identityʳ prefix)) ps≡) value)
    (yes (success prefix read read≡ value (c ∷ suffix) ps≡)) →
      no λ where
        o → ‼
          let @0 ps≡' : prefix ++ c ∷ suffix ≡ xs ++ []
              ps≡' = trans ps≡ (sym (++-identityʳ xs))
          in
          contradiction{P = _≡_{A = List UInt8} (c ∷ suffix) []}
              (Lemmas.++-cancel≡ˡ _ _ (TLV.nosubstrings ps≡' value o) ps≡')
              λ ()
