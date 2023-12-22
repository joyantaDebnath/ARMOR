{-# OPTIONS  --sized-types #-}

open import Armor.Binary
open import Armor.Data.X509
open import Armor.Data.X509.Semantic.Chain.NameMatch
open import Armor.Data.X509.Semantic.Chain.TCB
open import Armor.Prelude
import      Data.List as List

module Armor.Data.X509.Semantic.Chain.Properties where

-- Lemmas for uniqueness
─-preserves-distinct : {A : Set} ⦃ _ : Eq A ⦄ {x y : A} (xs : List A) → All (y ≢_) xs → (x∈ : x ∈ xs) → All (y ≢_) (xs Any.─ x∈)
─-preserves-distinct {x = x} {y} .(_ ∷ _) (px₁ ∷ distinct) (here px) = distinct
─-preserves-distinct {x = x} {y} .(_ ∷ _) (px ∷ distinct) (there x∈) = px ∷ ─-preserves-distinct _ distinct x∈

unique─ : {A : Set} ⦃ _ : Eq A ⦄ {x : A} (xs : List A) → List.Unique _≟_ xs → (x∈ : x ∈ xs) → List.Unique _≟_ (xs Any.─ x∈)
unique─ .(_ ∷ _) (x ∷ unique) (here refl) = unique
unique─ .(_ ∷ _) (x ∷ unique) (there x∈) = ─-preserves-distinct _ x x∈ ∷ unique─ _ unique x∈

∈xs─⇒∈xs : ∀ {ℓ} {A : Set ℓ} {x} {xs : List A} {i : Fin (length xs)} → x ∈ xs List.─ i → x ∈ xs
∈xs─⇒∈xs {xs = x ∷ xs} {i = Fin.zero} x∈xs─i = there x∈xs─i
∈xs─⇒∈xs {xs = x ∷ xs} {i = Fin.suc i} (here px) = here px
∈xs─⇒∈xs {xs = x ∷ xs} {i = Fin.suc i} (there x∈xs─i) = there (∈xs─⇒∈xs{i = i} x∈xs─i)

∈toList⇒ : ∀ trustedRoot candidates {@0 bs₁ bs₂} (issuee : Cert bs₁) {cert : Cert bs₂} → (chain : Chain trustedRoot candidates issuee)
           → (-, cert) ∈ toList chain → _≡_{A = Exists─ _ Cert} (-, cert) (-, issuee) ⊎ (-, cert) ∈ candidates ⊎ (-, cert) ∈ trustedRoot
∈toList⇒ trustedRoot candidates issuee (root ((─ _ , issuer) , isIssuer , isIn)) (here px) = inj₁ px
∈toList⇒ trustedRoot candidates issuee (root ((─ _ , issuer) , isIssuer , isIn)) (there (here refl)) = inj₂ (inj₂ isIn)
∈toList⇒ trustedRoot candidates issuee (link issuer isIn chain) (here refl) = inj₁ refl
∈toList⇒ trustedRoot candidates issuee (link issuer isIn chain) (there cert∈) = inj₂ (case ih of λ where
  (inj₁ refl) → inj₁ (proj₂ isIn)
  (inj₂ (inj₁ cert∈candidates─)) → inj₁ (∈removeCertFromCerts⇒ candidates cert∈candidates─)
  (inj₂ (inj₂ cert∈trustedRemoveIssuee)) → inj₂ (∈removeCertFromCerts⇒ trustedRoot cert∈trustedRemoveIssuee))
  where
  ih = ∈toList⇒ _ _ issuer chain cert∈

unique⇒x∉[xs─x∈] : ∀ {A : Set} ⦃ _ : Eq A ⦄ {x : A} {xs : List A} → List.Unique _≟_ xs → (x∈ : x ∈ xs) → x ∉ (xs Any.─ x∈)
unique⇒x∉[xs─x∈] {x = x} {.(_ ∷ _)} (all≢x ∷ unique) (here refl) x∈' =
  contradiction x∈' (All.All¬⇒¬Any all≢x)
unique⇒x∉[xs─x∈] {x = x} {.(x ∷ _)} (all≢x ∷ unique) (there {x = .x} x∈) (here refl) =
  contradiction x∈ (All.All¬⇒¬Any all≢x)
unique⇒x∉[xs─x∈] {x = x} {.(y ∷ _)} (all≢y ∷ unique) (there {x = y} x∈) (there x∈') =
  unique⇒x∉[xs─x∈] unique x∈ x∈'

chainUnique : ∀ trustedRoot candidates
              → ∀ {@0 bs} {issuee : Cert bs}
              → (-, issuee) ∉ candidates → (-, issuee) ∉ trustedRoot
              → (c : Chain trustedRoot candidates issuee) → ChainUnique c
chainUnique trustedRoot candidates issuee∉ca issuee∉tr (root (anIssuerForIn issuer isIssuerFor issuer∈)) =
  ((λ where refl → contradiction issuer∈ issuee∉tr) ∷ []) ∷ [] ∷ []
chainUnique trustedRoot candidates {issuee = issuee} issuee∉ca issuee∉tr (link issuer (isIssuer , isIn) c) =
  All.tabulate help ∷ ih
  where
  help : {cert : Exists─ _ Cert} → cert ∈ toList c → (-, issuee) ≢ cert
  help{cert} cert∈ refl = case ∈toList⇒ _ _ _ c cert∈ of λ where
    (inj₁ refl) → contradiction isIn issuee∉ca
    (inj₂ (inj₁ cert∈ca)) → contradiction (∈removeCertFromCerts⇒ candidates cert∈ca) issuee∉ca
    (inj₂ (inj₂ cert∈tr)) → contradiction (∈removeCertFromCerts⇒ trustedRoot cert∈tr) issuee∉tr

  ih : ChainUnique c
  ih = chainUnique (removeCertFromCerts issuer trustedRoot) (removeCertFromCerts issuer candidates)
         (∉removeCertFromCerts issuer candidates) (∉removeCertFromCerts issuer trustedRoot)
         c
