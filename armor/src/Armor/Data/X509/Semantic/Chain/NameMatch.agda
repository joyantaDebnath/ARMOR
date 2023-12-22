{-# OPTIONS --sized-types #-}

open import Armor.Binary
open import Armor.Data.X509.Name
open import Armor.Data.X509.Semantic.StringPrep.ExecDS
open import Armor.Data.X509.Semantic.StringPrep.ExecPS
open import Armor.Data.X509.Semantic.StringPrep.ExecIS
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.Sequence
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.SetOf
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Parallel
open import Armor.Prelude

module Armor.Data.X509.Semantic.Chain.NameMatch where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.IList       UInt8
open Armor.Grammar.Parallel    UInt8

{- https://datatracker.ietf.org/doc/html/rfc5280#section-7.1
-- Two naming attributes match if the attribute types are the same and
-- the values of the attributes are an exact match after processing with
-- the string preparation algorithm.
-}

ATVParamMatch : ∀ {@0 bs₁ bs₂ bs₃} → (o : OID bs₁) → (d : Dec ((-, TLV.val o) ∈ Name.RDN.ATV.OIDs.Supported)) → Name.RDN.ATVParam o d bs₂ → Name.RDN.ATVParam o d bs₃ → Set
ATVParamMatch o Name.RDN.atvParamUnsupported x x₁ = CompareDS x x₁
ATVParamMatch o Name.RDN.atvParamX520DNQualifier x x₁ = ComparePS x x₁
ATVParamMatch o Name.RDN.atvParamX520CountryName (mk×ₚ fstₚ₁ sndₚ₁) (mk×ₚ fstₚ₂ sndₚ₂) = ComparePS fstₚ₁ fstₚ₂
ATVParamMatch o Name.RDN.atvParamX520SerialNumber x x₁ = ComparePS x x₁
ATVParamMatch o Name.RDN.atvParamPCKS9Email x x₁ = CompareIS x x₁
ATVParamMatch o Name.RDN.atvParamDomainComponent x x₁ = CompareIS x x₁

atvParamMatch? : ∀ {@0 bs₁ bs₂ bs₃} → (o : OID bs₁) → (d : Dec ((-, TLV.val o) ∈ Name.RDN.ATV.OIDs.Supported))
                 → (p₁ : Name.RDN.ATVParam o d bs₂) → (p₂ : Name.RDN.ATVParam o d bs₃)
                 → Dec (ATVParamMatch o d p₁ p₂)
atvParamMatch? o (no ¬p) x x₁ = CompareDS-dec x x₁
atvParamMatch? o (yes (here px)) x x₁ = ComparePS-dec x x₁
atvParamMatch? o (yes (there (here px))) (mk×ₚ fstₚ₁ sndₚ₁) (mk×ₚ fstₚ₂ sndₚ₂) = ComparePS-dec fstₚ₁ fstₚ₂
atvParamMatch? o (yes (there (there (here px)))) x x₁ = ComparePS-dec x x₁
atvParamMatch? o (yes (there (there (there (here px))))) x x₁ = CompareIS-dec x x₁
atvParamMatch? o (yes (there (there (there (there (here px)))))) x x₁ = CompareIS-dec x x₁


ATVMatch : ∀ {@0 bs₁ bs₂} → Name.RDN.ATV bs₁ → Name.RDN.ATV bs₂ → Set
ATVMatch (mkTLV len (Sequence.mkOIDDefinedFields oid param bs≡₂) len≡ bs≡) (mkTLV len₁ (Sequence.mkOIDDefinedFields oid₁ param₁ bs≡₃) len≡₁ bs≡₁)
  = Σ (_≋_ {A = OID} oid oid₁) (λ where ≋-refl → ATVParamMatch oid ((-, TLV.val oid) ∈? Name.RDN.ATV.OIDs.Supported) param param₁)

atvMatch? : ∀ {@0 bs₁ bs₂} → (n : Name.RDN.ATV bs₁) → (m : Name.RDN.ATV bs₂) → Dec (ATVMatch n m)
atvMatch? (mkTLV len (Sequence.mkOIDDefinedFields oid param bs≡₂) len≡ bs≡) (mkTLV len₁ (Sequence.mkOIDDefinedFields oid₁ param₁ bs≡₃) len≡₁ bs≡₁)
  = case (_≋?_ {A = OID} oid oid₁) of λ where
      (no ¬p) → no λ { (fst , snd) → contradiction fst ¬p}
      (yes ≋-refl) →
        case atvParamMatch? oid ((-, TLV.val oid) ∈? Name.RDN.ATV.OIDs.Supported) param param₁ of λ where
          (no ¬p) → no λ where (≋-refl , snd) → contradiction snd ¬p
          (yes p) → yes (≋-refl , p)


{-  https://datatracker.ietf.org/doc/html/rfc5280#section-7.1
--                                    Two relative distinguished names
-- RDN1 and RDN2 match if they have the same number of naming attributes
-- and for each naming attribute in RDN1 there is a matching naming
-- attribute in RDN2.
-}

infix 4 _ATV∈_ _ATV∈?_ _ContainsAllATV_ _ContainsAllATV?_
data _ATV∈_ {@0 bs} (a : Name.RDN.ATV bs) : {@0 b : List UInt8} → SequenceOf Name.RDN.ATV b → Set where
  here  : ∀ {@0 bs₁ bs₂ bs₃} {x : Name.RDN.ATV bs₁} {xs : SequenceOf Name.RDN.ATV bs₂} (px : ATVMatch a x) (@0 bs≡ : bs₃ ≡ bs₁ ++ bs₂) → a ATV∈ (cons (mkSequenceOf x xs bs≡))
  there : ∀ {@0 bs₁ bs₂ bs₃} {x : Name.RDN.ATV bs₁} {xs : SequenceOf Name.RDN.ATV bs₂} (pxs : a ATV∈ xs) (@0 bs≡ : bs₃ ≡ bs₁ ++ bs₂) → a ATV∈ (cons (mkSequenceOf x xs bs≡))

_ATV∈?_ : ∀ {@0 bs} (atv : Name.RDN.ATV bs) → {@0 b : List UInt8} → (atvs : SequenceOf Name.RDN.ATV b) → Dec (atv ATV∈ atvs)
_ATV∈?_ a nil = no (λ ())
_ATV∈?_ a (cons (mkIListCons {bs₂ = g} head₁ tail₁ bs≡)) = case atvMatch? a head₁ of λ where
  (no ¬p) → case (a ATV∈?  tail₁) ret (const _) of λ where
    (no ¬q) → no λ where
      (here px .bs≡) → contradiction px ¬p
      (there x .bs≡) → contradiction x ¬q
    (yes p) → yes (there p bs≡)
  (yes p) → yes (here p bs≡)


data _ContainsAllATV_ {@0 bs} (xs : SequenceOf Name.RDN.ATV bs) : {@0 b : List UInt8} → SequenceOf Name.RDN.ATV b → Set where
  []  : xs ContainsAllATV nil
  cons : ∀ {@0 bs₁ bs₂ bs₃} {x : Name.RDN.ATV bs₁} {xs' : SequenceOf Name.RDN.ATV bs₂} (px : x ATV∈ xs) (pxs : xs ContainsAllATV xs') (@0 bs≡ : bs₃ ≡ bs₁ ++ bs₂) → xs ContainsAllATV (cons (mkSequenceOf x xs' bs≡))

_ContainsAllATV?_ : ∀ {@0 bs} (atvs₁ : SequenceOf Name.RDN.ATV bs) → {@0 b : List UInt8} → (atvs₂ : SequenceOf Name.RDN.ATV b) → Dec (atvs₁ ContainsAllATV atvs₂)
_ContainsAllATV?_ xs nil = yes []
_ContainsAllATV?_ xs (cons (mkIListCons head₁ tail₁ bs≡)) = case (head₁ ATV∈? xs) of λ where
  (no ¬p) → no λ where
    (cons px z bs≡) → contradiction px ¬p
  (yes p) → case xs ContainsAllATV?  tail₁ of λ where
    (no ¬p) → no λ where
      (cons px z bs≡) → contradiction z ¬p
    (yes q) → yes (cons p q bs≡)

RDNMatch : ∀ {@0 bs₁ bs₂} → Name.RDN bs₁ → Name.RDN bs₂ → Set
RDNMatch rdn₁ rdn₂ =
    SetOfFields.length (TLV.val rdn₁) ≡ SetOfFields.length (TLV.val rdn₂)
  × SetOfFields.toSequenceOf (TLV.val rdn₁) ContainsAllATV SetOfFields.toSequenceOf (TLV.val rdn₂)

rdnMatch? : ∀ {@0 bs₁ bs₂} → (n₁ : Name.RDN bs₁) (n₂ : Name.RDN bs₂) → Dec (RDNMatch n₁ n₂)
rdnMatch? n₁ n₂ = _ ≟ _ ×-dec _ ContainsAllATV? _

{-
--       A distinguished name DN1 is within the subtree defined by the
-- distinguished name DN2 if DN1 contains at least as many RDNs as DN2,
-- and DN1 and DN2 are a match when trailing RDNs in DN1 are ignored.
-}

NameFieldsMatch : ∀ {@0 bs₁ bs₂} → SequenceOfFields Name.RDN bs₁ → SequenceOfFields Name.RDN bs₂ → Set
NameFieldsMatch (mkSequenceOf h nil bs≡) (mkSequenceOf h₁ nil bs≡₁) = RDNMatch h h₁
NameFieldsMatch (mkSequenceOf h nil bs≡) (mkSequenceOf h₁ (cons x) bs≡₁) = RDNMatch h h₁
NameFieldsMatch (mkSequenceOf h (cons x) bs≡) (mkSequenceOf h₁ nil bs≡₁) = RDNMatch h h₁
NameFieldsMatch (mkSequenceOf h (cons x) bs≡) (mkSequenceOf h₁ (cons x₁) bs≡₁) = RDNMatch h h₁ × NameFieldsMatch x x₁

nameFieldsMatch? : ∀ {@0 bs₁ bs₂} → (nfs₁ : SequenceOfFields Name.RDN bs₁) → (nfs₂ : SequenceOfFields Name.RDN bs₂)
                   → Dec (NameFieldsMatch nfs₁ nfs₂)
nameFieldsMatch? (mkSequenceOf rdn₁ nil _) (mkSequenceOf rdn₂ nil _) = rdnMatch? rdn₁ rdn₂
nameFieldsMatch? (mkSequenceOf rdn₁ nil _) (mkSequenceOf rdn₂ (cons _) _) = rdnMatch? rdn₁ rdn₂
nameFieldsMatch? (mkSequenceOf rdn₁ (cons rdns₁) _) (mkSequenceOf rdn₂ nil _) = rdnMatch? rdn₁ rdn₂
nameFieldsMatch? (mkSequenceOf rdn₁ (cons rdns₁) _) (mkSequenceOf rdn₂ (cons rdns₂) _) =
  rdnMatch? rdn₁ rdn₂ ×-dec nameFieldsMatch? rdns₁ rdns₂

NameMatch : ∀ {@0 bs₁ bs₂} → Name bs₁ → Name bs₂ → Set
NameMatch (mkTLV len nil len≡ bs≡) (mkTLV len₁ nil len≡₁ bs≡₁) = ⊤
NameMatch (mkTLV len nil len≡ bs≡) (mkTLV len₁ (cons x) len≡₁ bs≡₁) = ⊥
NameMatch (mkTLV len (cons x) len≡ bs≡) (mkTLV len₁ nil len≡₁ bs≡₁) = ⊥
NameMatch (mkTLV len (cons x) len≡ bs≡) (mkTLV len₁ (cons x₁) len≡₁ bs≡₁) = NameFieldsMatch x x₁

nameMatch? : ∀ {@0 bs₁ bs₂} → (n₁ : Name bs₁) → (n₂ : Name bs₂) → Dec (NameMatch n₁ n₂)
nameMatch? (mkTLV _ nil _ _) (mkTLV _ nil _ _) = yes tt
nameMatch? (mkTLV _ nil _ _) (mkTLV _ (cons _) _ _) = no λ ()
nameMatch? (mkTLV _ (cons nfs₁) _ _) (mkTLV _ nil _ _) = no λ ()
nameMatch? (mkTLV _ (cons nfs₁) _ _) (mkTLV _ (cons nfs₂) _ _) = nameFieldsMatch? nfs₁ nfs₂
