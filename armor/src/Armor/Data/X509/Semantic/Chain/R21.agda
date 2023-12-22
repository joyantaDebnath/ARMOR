{-# OPTIONS --sized-types #-}

open import Armor.Binary
open import Armor.Data.X509
open import Armor.Data.X690-DER
open import Armor.Data.X509.Semantic.Cert.Utils
  using (isCRLSignPresent)
import      Armor.Data.X509.Semantic.Chain.TCB as Chain
import      Armor.Grammar.IList
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel

open import Armor.Prelude

open Armor.Grammar.IList    UInt8
open Armor.Grammar.Option   UInt8
open Armor.Grammar.Parallel UInt8

module Armor.Data.X509.Semantic.Chain.R21 where

helperR21₁-h : ∀ {@0 h t} → Extension.CRLDistPoint.DistPoint h → IList Extension.CRLDistPoint.DistPoint t  → Set
helperR21₁-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn none bs≡₁) len≡ bs≡) x₁ = ⊥
helperR21₁-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn (some x) bs≡₁) len≡ bs≡) nil = ⊤ 
helperR21₁-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn (some x) bs≡₁) len≡ bs≡) (cons (mkIListCons head₁ tail₁ bs≡₂)) = helperR21₁-h head₁ tail₁
  
helperR21₁ : Exists─ (List UInt8) (Option ExtensionFieldCRLDist) → Set
helperR21₁ (─ .[] , none) = ⊤
helperR21₁ (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ (cons (mkIListCons head₁ tail₁ bs≡₄)) snd₁) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helperR21₁-h head₁ tail₁

helperR21₂-h : ∀ {@0 h t} → Extension.CRLDistPoint.DistPoint h → IList Extension.CRLDistPoint.DistPoint t  → Set
helperR21₂-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields none crldprsn none bs≡₁) len≡ bs≡) x₁ = ⊥
helperR21₂-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields none crldprsn (some x) bs≡₁) len≡ bs≡) x₁ = ⊥
helperR21₂-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x) crldprsn none bs≡₁) len≡ bs≡) nil = ⊤
helperR21₂-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x) crldprsn none bs≡₁) len≡ bs≡) (cons (mkIListCons head₁ tail₁ bs≡₂)) = helperR21₂-h head₁ tail₁
helperR21₂-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x) crldprsn (some y) bs≡₁) len≡ bs≡) x₁ = ⊥

helperR21₂ : Exists─ (List UInt8) (Option ExtensionFieldCRLDist) → Set
helperR21₂ (─ .[] , none) = ⊤
helperR21₂ (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ (cons (mkIListCons head₁ tail₁ bs≡₄)) snd₁) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helperR21₂-h head₁ tail₁

helperR21 : (c : List (Exists─ (List UInt8) Cert)) → Set
helperR21 [] = ⊥
helperR21 (x₁ ∷ []) = ⊤
helperR21 (x₁ ∷ x₂ ∷ t) with helperR21 (x₂ ∷ t) | isCRLSignPresent (Cert.getKU (proj₂ x₂))
... | rec | true =  helperR21₂ (Cert.getCRLDIST (proj₂ x₁)) × rec
... | rec | false = helperR21₁ (Cert.getCRLDIST (proj₂ x₁)) × rec

helperR21₂-h-dec : ∀ {@0 h t} → (a : Extension.CRLDistPoint.DistPoint h) → (b : IList Extension.CRLDistPoint.DistPoint t)  → Dec (helperR21₂-h a b)
helperR21₂-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields none crldprsn none bs≡₁) len≡ bs≡) x₁ = no (λ())
helperR21₂-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields none crldprsn (some x) bs≡₁) len≡ bs≡) x₁ = no (λ())
helperR21₂-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x) crldprsn none bs≡₁) len≡ bs≡) nil = yes tt
helperR21₂-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x) crldprsn none bs≡₁) len≡ bs≡) (cons (mkIListCons head₁ tail₁ bs≡₂)) = helperR21₂-h-dec head₁ tail₁
helperR21₂-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x) crldprsn (some y) bs≡₁) len≡ bs≡) x₁ = no (λ())

helperR21₂-dec : (c : Exists─ (List UInt8) (Option ExtensionFieldCRLDist)) → Dec (helperR21₂ c)
helperR21₂-dec (─ .[] , none) = yes tt
helperR21₂-dec (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ (cons (mkIListCons head₁ tail₁ bs≡₄)) snd₁) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helperR21₂-h-dec head₁ tail₁

helperR21₁-h-dec : ∀ {@0 h t} → (a : Extension.CRLDistPoint.DistPoint h) → (b : IList Extension.CRLDistPoint.DistPoint t)  → Dec (helperR21₁-h a b)
helperR21₁-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn none bs≡₁) len≡ bs≡) x₁ = no (λ())
helperR21₁-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn (some x) bs≡₁) len≡ bs≡) nil = yes tt 
helperR21₁-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn (some x) bs≡₁) len≡ bs≡) (cons (mkIListCons head₁ tail₁ bs≡₂)) = helperR21₁-h-dec head₁ tail₁

helperR21₁-dec : (c : Exists─ (List UInt8) (Option ExtensionFieldCRLDist)) → Dec (helperR21₁ c)
helperR21₁-dec (─ .[] , none) = yes tt
helperR21₁-dec (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ (cons (mkIListCons head₁ tail₁ bs≡₄)) snd₁) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helperR21₁-h-dec head₁ tail₁

helperR21-dec : (c : List (Exists─ (List UInt8) Cert)) → Dec (helperR21 c)
helperR21-dec [] = no λ()
helperR21-dec (x₁ ∷ []) = yes tt
helperR21-dec (x₁ ∷ x₂ ∷ t) with helperR21-dec (x₂ ∷ t) | isCRLSignPresent (Cert.getKU (proj₂ x₂))
... | rec | true = helperR21₂-dec (Cert.getCRLDIST (proj₂ x₁)) ×-dec rec
... | rec | false = helperR21₁-dec (Cert.getCRLDIST (proj₂ x₁)) ×-dec rec

open Chain using (Chain)

module _ {trust candidates : List (Exists─ _ Cert)} {@0 bs} (issuee : Cert bs) where

  R21 : Chain trust candidates issuee → Set
  R21 c = helperR21 (Chain.toList c)
  
  r21 : Decidable R21
  r21 c = helperR21-dec (Chain.toList c)
