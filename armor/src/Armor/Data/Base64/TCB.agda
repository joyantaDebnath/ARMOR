open import Armor.Binary
import      Armor.Grammar.IList
open import Armor.Prelude

module Armor.Data.Base64.TCB where

open Armor.Grammar.IList Char

record Base64Char (@0 bs : List Char) : Set where
  constructor mk64
  field
    @0 c : Char
    @0 c∈ : c ∈ Base64.charset
    i : Singleton (Any.index c∈)
    @0 bs≡ : bs ≡ [ c ]

pattern mk64! {c} {c∈} i = mk64 c c∈ i refl

record Base64Pad2 (@0 bs : List Char) : Set where
  constructor mk64P2
  field
    @0 {b₁ b₂} : Char
    c₁ : Base64Char [ b₁ ]
    c₂ : Base64Char [ b₂ ]
    @0 pad : toℕ (↑ Base64Char.i c₂) % (2 ^ 4) ≡ 0
    @0 bs≡ : bs ≡ b₁ ∷ b₂ ∷ '=' ∷ [ '=' ]

record Base64Pad1 (@0 bs : List Char) : Set where
  constructor mk64P1
  field
    @0 {b₁ b₂ b₃} : Char
    c₁ : Base64Char [ b₁ ]
    c₂ : Base64Char [ b₂ ]
    c₃ : Base64Char [ b₃ ]
    @0 pad : toℕ (↑ Base64Char.i c₃) % (2 ^ 2) ≡ 0
    @0 bs≡ : bs ≡ b₁ ∷ b₂ ∷ b₃ ∷ [ '=' ]

data Base64Pad (@0 bs : List Char) : Set where
  pad0 : bs ≡ []       → Base64Pad bs
  pad1 : Base64Pad1 bs → Base64Pad bs
  pad2 : Base64Pad2 bs → Base64Pad bs

pattern mk64P1! {c₁} {c₂} {c₃} {p} = pad1 (mk64P1 c₁ c₂ c₃ p refl)
pattern mk64P2! {c₁} {c₂} {p} = pad2 (mk64P2 c₁ c₂ p refl)

record Base64Str (@0 bs : List Char) : Set where
  constructor mk64Str
  field
    @0 {s p} : List Char
    str : IList Base64Char s
    @0 strLen : length s % 4 ≡ 0
    pad : Base64Pad p
    @0 bs≡ : bs ≡ s ++ p

pattern consBase64Str {c₁} {c₁∈} i₁ {c₂} {c₂∈} i₂ {c₃} {c₃∈} i₃ {c₄} {c₄∈} i₄ s l p bs≡ =
  mk64Str (consIList (mk64!{c₁}{c₁∈} i₁) (consIList (mk64!{c₂}{c₂∈} i₂) (consIList (mk64!{c₃}{c₃∈} i₃) (consIList (mk64!{c₄}{c₄∈} i₄) s refl) refl) refl) refl) l p bs≡

decodeStr : ∀ {@0 bs} → Base64Str bs → List UInt8
decodeStr (mk64Str str strLen pad bs≡) =
  helper₁ str strLen ++ helper₂ pad
  where
  open import Armor.Binary.Base64EncDec.EncDec.TCB
  helper₁ : ∀ {@0 bs} → IList Base64Char bs → @0 length bs % 4 ≡ 0
            → List UInt8
  helper₁ nil refl = []
  helper₁ (cons (mkIListCons (mk64 _ _ i refl) (cons (mkIListCons (mk64 _ _ i₁ refl) (cons (mkIListCons (mk64 _ _ i₂ refl) (cons (mkIListCons (mk64 _ _ i₃ refl) tail₁ refl)) refl)) refl)) refl)) pf =
       Base64.decode (↑ i ∷ ↑ i₁ ∷ ↑ i₂ ∷ [ ↑ i₃ ]) tt
    ++ helper₁ tail₁ pf

  helper₂ : ∀ {@0 bs} → Base64Pad bs → List UInt8
  helper₂ (pad0 x) = []
  helper₂ (pad1 (mk64P1 (mk64 _ _ i _) (mk64 _ _ i₁ _) (mk64 _ _ i₂ _) _ _)) =
    from-just (base64To256 ((↑ i) ∷ (↑ i₁) ∷ [ ↑ i₂ ]))
  helper₂ (pad2 (mk64P2 (mk64 _ _ i _) (mk64 _ _ i₁ _) _ _)) =
    from-just (base64To256 (↑ i ∷ [ ↑ i₁ ]))
