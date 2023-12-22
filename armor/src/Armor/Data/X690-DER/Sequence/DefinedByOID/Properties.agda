open import Armor.Binary
open import Armor.Data.X690-DER.OID.TCB
import      Armor.Data.X690-DER.OID.Properties as OID
open import Armor.Data.X690-DER.Sequence.DefinedByOID.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.TLV.Properties as TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
open import Armor.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X690-DER.Sequence.DefinedByOID.Properties
  (P : AnyDefinedByOID)
  where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Seq         UInt8

iso : Iso (DefinedByOIDFieldsRep P) (DefinedByOIDFields P)
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkOIDDefinedFields algOID param bs≡) = refl

@0 unambiguous
  : (∀ {@0 bs} → (o : OID bs) → Unambiguous (P o))
    → Unambiguous (DefinedByOIDFields P)
unambiguous ua =
  Iso.unambiguous iso
    (Seq.unambiguousᵈ OID.unambiguous TLV.nosubstrings ua)

@0 nosubstrings : (∀ {@0 bs} → (a : OID bs) → NoSubstrings (P a))
                  → NoSubstrings (DefinedByOIDFields P)
nosubstrings ns =
  Iso.nosubstrings equivalent (Seq.nosubstringsᵈ TLV.nosubstrings OID.unambiguous ns)

@0 noConfusionFieldsParam
  : {@0 P' : {@0 bs : List UInt8} → OID bs → @0 List UInt8 → Set}
    → (∀ {@0 bs bs' bs“} → (o : OID bs) → P o bs' → ¬ P' o bs“)
    → NoConfusion (DefinedByOIDFields P) (DefinedByOIDFields P')
noConfusionFieldsParam{P'} excl {xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ (mkOIDDefinedFields{bs₁}{p} o para bs≡) (mkOIDDefinedFields{bs₁'}{p'} o' para' bs'≡) =
     let
       @0 ++≡ : bs₁ ++ p ++ ys₁ ≡ bs₁' ++ p' ++ ys₂
       ++≡ = begin
         bs₁ ++ p ++ ys₁ ≡⟨ solve (++-monoid UInt8) ⟩
         (bs₁ ++ p) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
         xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
         xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs'≡ ⟩
         (bs₁' ++ p') ++ ys₂ ≡⟨ solve (++-monoid UInt8) ⟩
         bs₁' ++ p' ++ ys₂ ∎
  
       @0 bs₁≡ : bs₁ ≡ bs₁'
       bs₁≡ = TLV.nosubstrings ++≡ o o'
  
       o≋o' : _≋_{OID} o o'
       o≋o' = mk≋ bs₁≡ (OID.unambiguous _ o')
     in
     contradiction
       (case o≋o' ret (const _) of λ where
         ≋-refl → para')
       (excl o para)
  where
  open ≡-Reasoning

@0 noConfusionParam
  : {@0 P' : {@0 bs : List UInt8} → OID bs → @0 List UInt8 → Set}
    → (∀ {@0 bs bs' bs“} → (o : OID bs) → P o bs' → ¬ P' o bs“)
    → NoConfusion (DefinedByOID P) (DefinedByOID P')
noConfusionParam excl = TLV.noconfusionVal (noConfusionFieldsParam excl)

@0 nonmalleableFields : {R : Raw₁ RawOID P} → NonMalleable₁ R
                        → NonMalleable (RawDefinedByOIDFields R)
nonmalleableFields{R} N =
  Iso.nonmalleable iso (Raw&ₚᵈ RawOID R)
    (Seq.nonmalleableᵈ OID.nonmalleable N)

@0 nonmalleable
  : ∀ t {R : Raw₁ RawOID P} → NonMalleable₁ R
    → NonMalleable (RawTLV t (RawDefinedByOIDFields R))
nonmalleable t N = TLV.nonmalleable (nonmalleableFields N)

eq≋ : (∀ {@0 bs} → (o : OID bs) → Eq≋ (P o)) → Eq≋ (DefinedByOIDFields P)
eq≋ eqP = Eq⇒Eq≋ (Iso.isoEq iso (Seq.eq&ₚᵈ it λ a → Eq≋⇒Eq (eqP a)))
