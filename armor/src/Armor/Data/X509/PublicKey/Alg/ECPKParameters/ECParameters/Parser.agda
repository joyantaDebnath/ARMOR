open import Armor.Binary
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Properties
open import Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.TCB
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Parser where

open Armor.Grammar.Definitions              UInt8
open Armor.Grammar.Option                   UInt8
open Armor.Grammar.Parallel                 UInt8
open Armor.Grammar.Parser                   UInt8
open Armor.Grammar.Properties               UInt8
open Armor.Grammar.Seq                      UInt8

private
  here' = "X509: PublicKey: Alg: ECPKParameters: ECParameters"

parseFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength ECParametersFields n)
parseFields n =
  parseEquivalent
    (Iso.transEquivalent (Iso.symEquivalent Distribute.exactLength-&) (Parallel.equivalent₁ reassoc))
    (parse&ᵈ{A = Length≤ (&ₚ (λ x → Erased (x ≡ # 2 ∷ # 1 ∷ [ # 1 ])) (&ₚ FieldID (&ₚ Curve (&ₚ OctetString Int)))) n}
      (Parallel.nosubstrings₁
        (Seq.nosubstrings (λ where _ (─ refl) (─ refl) → refl)
        (Seq.nosubstrings TLV.nosubstrings
        (Seq.nosubstrings TLV.nosubstrings
        (Seq.nosubstrings TLV.nosubstrings
                          TLV.nosubstrings)))))
      (Parallel.Length≤.unambiguous _
        (Seq.unambiguous (erased-unique ≡-unique) (λ where _ (─ refl) (─ refl) → refl)
        (Seq.unambiguous FieldID.unambiguous TLV.nosubstrings
        (Seq.unambiguous Curve.unambiguous TLV.nosubstrings
        (Seq.unambiguous OctetString.unambiguous TLV.nosubstrings
                         Int.unambiguous)))))
      (parse≤ n
        (parse&
          (λ where _ (─ refl) (─ refl) → refl)
          (parseLitE
            (tell $ here' String.++ ": underflow")
            (tell $ here' String.++ ": mismatch")
            (# 2 ∷ # 1 ∷ [ # 1 ]))
          (parse& TLV.nosubstrings FieldID.parse
          (parse& TLV.nosubstrings Curve.parse
          (parse& TLV.nosubstrings OctetString.parse
                                   (Int.parse here')))))
        (Seq.nosubstrings (λ where _ (─ refl) (─ refl) → refl)
        (Seq.nosubstrings TLV.nosubstrings
        (Seq.nosubstrings TLV.nosubstrings
        (Seq.nosubstrings TLV.nosubstrings
                          TLV.nosubstrings))))
        (tell $ here' String.++ ": overflow"))
      λ where
        {bs} (singleton r r≡) _ →
          subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength (Option Int) (n ∸ x)))
            r≡
            (Option.parseOption₁ExactLength
              TLV.nosubstrings
              (tell $ here' String.++ ": underflow")
              (Int.parse here') _))
  where
  Reassoc = &ₚ (&ₚ (λ x → Erased (x ≡ # 2 ∷ # 1 ∷ [ # 1 ])) (&ₚ FieldID (&ₚ Curve (&ₚ OctetString Int)))) (Option Int)

  reassoc : Equivalent Reassoc ECParametersFields
  proj₁ reassoc (mk&ₚ (mk&ₚ (─ refl) (mk&ₚ fieldID (mk&ₚ curve (mk&ₚ base order refl) refl) refl) refl) cofactor refl) =
    mkECParametersFields self fieldID curve base order cofactor
      (cong ((# 2 ∷ # 1 ∷ [ # 1 ]) ++_) (solve (++-monoid UInt8)))
  proj₂ reassoc (mkECParametersFields self fieldID curve base order cofactor refl) =
    mk&ₚ (mk&ₚ (─ refl) (mk&ₚ fieldID (mk&ₚ curve (mk&ₚ base order refl) refl) refl) refl) cofactor
      (cong ((# 2 ∷ # 1 ∷ [ # 1 ]) ++_) (solve (++-monoid UInt8)))

parse : Parser (Logging ∘ Dec) ECParameters
parse = parseTLV _ here' _ parseFields
