open import Armor.Binary
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.SetOf.Order.TCB
open import Armor.Data.X690-DER.SetOf.Properties
open import Armor.Data.X690-DER.SetOf.TCB
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude
import      Data.List.Relation.Unary.Sorted.TotalOrder as Sorted

module Armor.Data.X690-DER.SetOf.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.IList       UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Sorted                    bytesTotalOrder

module _ (caller : String) {A : @0 List UInt8 → Set} (@0 ne : NonEmpty A) (@0 ns : NoSubstrings A) (p : Parser (Logging ∘ Dec) A) where

  private
    here' = caller String.++ " (X690-DER: SetOf)"

  parseFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength (SetOfFields A) n)
  runParser (parseFields n) xs = do
    (yes (success pre₁ r₁ r₁≡ (mk×ₚ (mk×ₚ v₁ v₁Len≥1) (─ v₁BSLen)) suf₁ ps≡₁))
      ← runParser
          (parseBoundedSequenceOf (here' String.++ " (fields)")
            (A ×ₚ Singleton) (Parallel.nonempty₁ ne) (Parallel.nosubstrings₁ ns)
            (parse×Singleton p) n 1) xs
      where no ¬p → do
        tell $ here' String.++ " (fields): failed to parse (as SequenceOf)"
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ (mkSetOfFields elems order) (─ fieldsBSLen)) suffix ps≡) →
            contradiction
              (success prefix read read≡
                (mk×ₚ
                  (mk×ₚ
                    (mapIList (λ x → mk×ₚ x self) (fstₚ elems))
                    (subst₀! (λ x → (Erased (x ≥ 1))) (sym (IList.mapIListLength _ (fstₚ elems))) (sndₚ elems)))
                  (─ fieldsBSLen)) suffix ps≡)
              ¬p
    let
      elems' : SequenceOf A pre₁
      elems' = mapIList fstₚ v₁

      @0 ol₁ : List (List UInt8)
      ol₁ = orderingList₁ v₁

      ol₂ : List (List UInt8)
      ol₂ = orderingList₂ v₁

      @0 ol₁≡ol₂ : ol₁ ≡ ol₂
      ol₁≡ol₂ = orderingList≡ v₁

      elemsLen : Erased (lengthIList elems' ≥ 1)
      elemsLen = subst₀! (λ x → Erased (x ≥ 1)) (sym (IList.mapIListLength fstₚ v₁)) v₁Len≥1
    case sorted? _≲?_ ol₂ of λ where
      (no ¬sorted) → do
        tell $ here' String.++ " (fields): not sorted!"
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ so@(mkSetOfFields (mk×ₚ elems“ _) order) (─ fieldsBSLen)) suffix ps≡) →
            let
              @0 prefix≡ : prefix ≡ pre₁
              prefix≡ = proj₁ (Lemmas.length-++-≡ prefix suffix pre₁ suf₁ (trans ps≡ (sym ps≡₁)) (trans fieldsBSLen (sym v₁BSLen)))

              @0 ol“≡ : SetOfFields.orderingList so ≡ ol₂
              ol“≡ = caseErased prefix≡ ret (const _) of λ where
                refl → ─ orderingList≡' v₁ elems“
            in
            contradiction
              (subst Sorted ol“≡ (toWitness order))
              ¬sorted
      (yes sorted) → return (yes
        (success pre₁ r₁ r₁≡
          (mk×ₚ
            (mkSetOfFields (mk×ₚ elems' elemsLen)
              (subst₀ (λ x → True (sorted? _≲?_ x)) (sym ol₁≡ol₂) (fromWitness{Q = sorted? _≲?_ _} sorted)))
            (─ v₁BSLen))
          suf₁ ps≡₁))
    where
    @0 orderingList₁ : ∀ {@0 bs} → IList (A ×ₚ Singleton) bs → List (List UInt8)
    orderingList₁ v = liftMapErase{A = Exists─ _ A} proj₁ (toList (mapIList fstₚ v))

    orderingList₂ : ∀ {@0 bs} → IList (A ×ₚ Singleton) bs → List (List UInt8)
    orderingList₂ v = map{A = Exists─ _ (A ×ₚ Singleton)} (λ x → ↑ sndₚ (proj₂ x)) (toList v)

    @0 orderingList≡ : ∀ {@0 bs} → (v : IList (A ×ₚ Singleton) bs)
                       → _≡_{A = List (List UInt8)} (orderingList₁ v) (orderingList₂ v)
    orderingList≡ nil = refl
    orderingList≡ (consIList (mk×ₚ h (singleton bs refl)) t refl) =
      cong₂ _∷_ refl (orderingList≡ t)

    @0 orderingList≡' : ∀ {@0 bs} → (v : IList (A ×ₚ Singleton) bs) (elems : IList A bs)
                        → liftMapErase proj₁ (toList elems) ≡ orderingList₂ v
    orderingList≡' nil nil = refl
    orderingList≡' nil (consIList h₂ t₂ bs≡₂) =
      contradiction (++-conicalˡ _ _ (sym bs≡₂)) (ne h₂)
    orderingList≡' (consIList (mk×ₚ h₁ self) t₁ bs≡₁) nil =
      contradiction (++-conicalˡ _ _ (sym bs≡₁)) (ne h₁)
    orderingList≡' (consIList{bs₁ = bs₁₁} (mk×ₚ h₁ self) t₁ refl) (consIList{bs₁ = bs₁₂} h₂ t₂ bs≡₂) =
      caseErased ns (sym bs≡₂) h₂ h₁ ret (const _) of λ where
        refl → ─ (caseErased ++-cancelˡ bs₁₁ (‼ bs≡₂) ret (const _) of λ where
          refl → ─ (cong₂ _∷_ refl (orderingList≡' t₁ t₂)))

  parse : Parser (Logging ∘ Dec) (SetOf A)
  parse = parseTLV _ here' _ parseFields
