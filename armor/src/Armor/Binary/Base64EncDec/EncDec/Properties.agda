import      Armor.Binary.Base64EncDec.Base64           as Base64
import      Armor.Binary.Base64EncDec.EncDec.Bytes.TCB as Bytes
open import Armor.Binary.Base64EncDec.EncDec.TCB
open import Armor.Binary.Bits
open import Armor.Binary.UInt6
open import Armor.Binary.UInt8.TCB
open import Armor.Prelude

module Armor.Binary.Base64EncDec.EncDec.Properties where

base64To256∘base256To64 : (bs : List UInt8) → base64To256 (base256To64 bs) ≡ just bs
base64To256∘base256To64 [] = refl
base64To256∘base256To64 (x ∷ []) = begin
  base64To256 (base256To64 [ x ]) ≡⟨⟩
  base64To256 (y₁ ∷ [ y₂ ]) ≡⟨⟩
  just [ x' ]
    ≡⟨ cong (λ x → just [ x ]) (begin
         x' ≡⟨⟩
         fromBinary z ≡⟨ cong (fromBinary {8}) z≡ ⟩
         fromBinary{8} (toBinary x) ≡⟨ fromBinary∘toBinary{8} x ⟩
         x ∎) ⟩
  just [ x ] ∎
  where
  open ≡-Reasoning

  xb : Binary 8
  xb = toBinary x

  y : Vec UInt6 2
  y = Vec.map fromBinary (Bytes.pad256To64₁ xb)

  y₁ : UInt6
  y₁ = Vec.head y

  y₂ : UInt6
  y₂ = Vec.head (Vec.tail y)

  z : Binary 8
  z = Vec._++_{m = 6}{2} (toBinary y₁) (Vec.take 2{4} (toBinary y₂))

  z‼ : Fin 8 → Bool
  z‼ i = Vec.lookup z i

  z≡ : z ≡ xb
  z≡ = begin
    Vec._++_{m = 6}{2} (toBinary y₁) (Vec.take 2{4} (toBinary y₂)) ≡⟨⟩
    Vec.take 8 {4} ((toBinary{6} y₁) Vec.++ (toBinary{6} y₂)) ≡⟨⟩
    Vec.take 8 {4} ((toBinary {6} (fromBinary {6} (Vec.head (Bytes.pad256To64₁ xb))))
                   Vec.++ toBinary {6} (fromBinary {6} (Vec.lookup (Bytes.pad256To64₁ xb) (# 1))))
      ≡⟨ cong (Vec.take 8 {4})
           (cong₂ (Vec._++_ {m = 6} {n = 6})
             (toBinary∘fromBinary {6} (Vec.head (Bytes.pad256To64₁ xb)) )
             (toBinary∘fromBinary {6} (Vec.lookup (Bytes.pad256To64₁ xb) (# 1)))) ⟩
    Vec.take 8 {4} (Vec.lookup (Bytes.pad256To64₁ xb) (# 0)
                    Vec.++ Vec.lookup (Bytes.pad256To64₁ xb) (# 1)) ≡⟨⟩
    (xb ∎)

  x' : UInt8
  x' = fromBinary z
base64To256∘base256To64 (x ∷ x₁ ∷ []) = begin
  base64To256 (base256To64 (x ∷ [ x₁ ])) ≡⟨⟩
  base64To256 (y‼ (# 0) ∷ y‼ (# 1) ∷ [ y‼ (# 2) ]) ≡⟨⟩
  just (lookup z (# 0) ∷ [ lookup z (# 1)] ) ≡⟨ cong just z≡ ⟩
  just (x ∷ [ x₁ ]) ∎
  where
  open ≡-Reasoning

  xb  = toBinary{8} x
  x₁b = toBinary{8} x₁

  y = Vec.map fromBinary (Bytes.pad256To64₂ (xb , x₁b))

  y‼ : Fin 3 → UInt6
  y‼ = Vec.lookup y

  z : List UInt8
  z = map fromBinary (Bytes.pad64To256 (Base64.pad1 (toBinary (y‼ (# 0)) ∷ toBinary (y‼ (# 1)) ∷ Vec.[ toBinary (y‼ (# 2)) ])))

  z≡ : z ≡ x ∷ [ x₁ ]
  z≡ = begin
    map fromBinary (Bytes.pad64To256 (Base64.pad1 (toBinary (y‼ (# 0)) ∷ toBinary (y‼ (# 1)) ∷ Vec.[ toBinary (y‼ (# 2)) ])))
      ≡⟨⟩
        fromBinary{8} (toBinary{6} (y‼ (# 0)) Vec.++ Vec.take 2 {4} (toBinary{6} (y‼ (# 1))))
    ∷ [ fromBinary {8} ((Vec.drop 2 {4} (toBinary{6} (y‼ (# 1)))) Vec.++ (Vec.take 4 {2} (toBinary{6} (y‼ (# 2))))) ] ≡⟨⟩
    fromBinary {8} ((toBinary {6} (fromBinary {6} (Vec.take 6 {2} xb)))
      Vec.++ (Vec.take 2 {4} (toBinary {6} (fromBinary {6} ((Vec.drop 6 {2} xb) Vec.++ (Vec.take 4 {4} x₁b))))))
    ∷ [ fromBinary {8} ((Vec.drop 2 {4} (toBinary {6} (fromBinary {6} ((Vec.drop 6 {2} xb) Vec.++ (Vec.take 4 {4} x₁b)))))
        Vec.++ (Vec.take 4 {2} (toBinary {6} (fromBinary {6} ((Vec.drop 4 {4} x₁b) Vec.++ (Vec.replicate #0)))))) ]
          ≡⟨ cong₂ _∷_
               (cong (fromBinary {8})
                 (cong₂ (Vec._++_ {m = 6} {2})
                   (toBinary∘fromBinary (Vec.take 6 {2} xb))
                   (cong (Vec.take 2 {4})
                     (toBinary∘fromBinary{6} ((Vec.drop 6 {2} xb) Vec.++ (Vec.take 4 {4} x₁b))))))
               (cong [_] (cong (fromBinary {8})
                 (cong₂ (Vec._++_ {m = 4} {4})
                   (cong (Vec.drop 2 {4})
                     (toBinary∘fromBinary ((Vec.drop 6 {2} xb) Vec.++ (Vec.take 4 {4} x₁b))))
                   (cong (Vec.take 4 {2})
                     (toBinary∘fromBinary {6} ((Vec.drop 4 {4} x₁b) Vec.++ (Vec.replicate #0))))))) ⟩
    fromBinary {8} (Vec.take 6 {2} xb Vec.++ Vec.take 2 {4} ((Vec.drop 6 {2} xb) Vec.++ (Vec.take 4 {4} x₁b)))
    ∷ [ fromBinary {8} ((Vec.drop 2 {4} (Vec.drop 6 {2} xb Vec.++ (Vec.take 4 {4} x₁b)))
        Vec.++ Vec.take 4 {2} (Vec.drop 4 {4} x₁b Vec.++ Vec.replicate #0)) ] ≡⟨⟩
    fromBinary{8} (toBinary{8} x) ∷ [ fromBinary{8} (toBinary{8} x₁)]
      ≡⟨ cong₂ (λ x y₁ → x ∷ [ y₁ ])
           (fromBinary∘toBinary{8} x)
           (fromBinary∘toBinary{8} x₁) ⟩
    x ∷ [ x₁ ] ∎

base64To256∘base256To64 (x ∷ x₁ ∷ x₂ ∷ bs) = begin
  base64To256 ((y‼ (# 0) ∷ y‼ (# 1) ∷ y‼ (# 2) ∷ [ y‼ (# 3) ]) ++ base256To64 bs) ≡⟨⟩
  maybe (λ ds → just (map fromBinary (Vec.toList z) ++ ds)) nothing (base64To256 (base256To64 bs))
    ≡⟨ cong (maybe (λ ds → just (map fromBinary (Vec.toList z) ++ ds)) nothing)
         (base64To256∘base256To64 bs) ⟩
  just (map fromBinary (Vec.toList z) ++ bs) ≡⟨⟩
  just w ≡⟨ cong just w≡ ⟩
  just (x ∷ x₁ ∷ x₂ ∷ bs) ∎
  where
  open ≡-Reasoning

  xb  = toBinary{8} x
  xb₁ = toBinary{8} x₁
  xb₂ = toBinary{8} x₂

  y : Vec (Binary 6) 4
  y = Bytes.base256To64 (xb ∷ xb₁ ∷ Vec.[ xb₂ ])

  y‼ : Fin 4 → UInt6
  y‼ i = fromBinary{6} (Vec.lookup y i)

  z : Vec (Binary 8) 3
  z = Bytes.base64To256 (toBinary{6} (y‼ (# 0)) ∷ toBinary{6} (y‼ (# 1)) ∷ toBinary{6} (y‼ (# 2)) ∷ Vec.[ toBinary{6} (y‼ (# 3)) ])

  w : List UInt8
  w = (fromBinary (Vec.lookup z (# 0)) ∷ fromBinary (Vec.lookup z (# 1)) ∷ fromBinary (Vec.lookup z (# 2)) ∷ bs)

  w≡ : w ≡ x ∷ x₁ ∷ x₂ ∷ bs
  w≡ = cong (_++ bs) (begin
    fromBinary (Vec.lookup z (# 0)) ∷ fromBinary (Vec.lookup z (# 1)) ∷ [ fromBinary (Vec.lookup z (# 2)) ]
      ≡⟨⟩
    fromBinary {8} (toBinary{6} (y‼ (# 0)) Vec.++ Vec.take 2 {4} (toBinary{6} (y‼ (# 1))))
    ∷ fromBinary{8} ((Vec.drop 2 {4} (toBinary {6} (y‼ (# 1)))) Vec.++ (Vec.take 4 {2} (toBinary{6} (y‼ (# 2)))))
    ∷ [ fromBinary {8} ((Vec.drop 4 {2} (toBinary{6} (y‼ (# 2)))) Vec.++ (toBinary {6} (y‼ (# 3)))) ]
      ≡⟨⟩
    fromBinary {8} (toBinary{6} (fromBinary{6} (Vec.lookup y (# 0))) Vec.++ Vec.take 2 {4} (toBinary{6} (fromBinary{6} (Vec.lookup y (# 1)))))
    ∷ fromBinary{8} ((Vec.drop 2 {4} (toBinary {6} (fromBinary{6} (Vec.lookup y (# 1))))) Vec.++ (Vec.take 4 {2} (toBinary{6} (fromBinary{6} (Vec.lookup y (# 2))))))
    ∷ [ fromBinary {8} ((Vec.drop 4 {2} (toBinary{6} (fromBinary{6} (Vec.lookup y (# 2))))) Vec.++ (toBinary {6} (fromBinary{6} (Vec.lookup y (# 3))))) ]
      ≡⟨ cong₂ _∷_
           (cong (fromBinary {8})
             (cong₂ (Vec._++_ {m = 6} {2})
               (toBinary∘fromBinary {6} (Vec.lookup y (# 0)))
               (cong (Vec.take 2 {4}) (toBinary∘fromBinary {6} (Vec.lookup y (# 1))))))
           (cong₂ _∷_
             (cong (fromBinary {8})
               (cong₂ (Vec._++_ {m = 4} {4})
                 (cong (Vec.drop 2 {4})
                   (toBinary∘fromBinary (Vec.lookup y (# 1))))
                 (cong (Vec.take 4 {2})
                   (toBinary∘fromBinary {6} (Vec.lookup y (# 2))))))
             (cong [_]
               (cong (fromBinary {8})
                 (cong₂ (Vec._++_ {m = 2} {6})
                   (cong (Vec.drop 4 {2})
                     (toBinary∘fromBinary {6} (Vec.lookup y (# 2))))
                   (toBinary∘fromBinary{6} (Vec.lookup y (# 3))))))) ⟩
    fromBinary {8} (Vec.lookup y (# 0) Vec.++ Vec.take 2 {4} (Vec.lookup y (# 1)))
    ∷ fromBinary {8} ((Vec.drop 2 {4} (Vec.lookup y (# 1))) Vec.++ (Vec.take 4 {2} (Vec.lookup y (# 2))))
    ∷ [ fromBinary {8} (Vec.drop 4 {2} (Vec.lookup y (# 2)) Vec.++ Vec.lookup y (# 3)) ]
      ≡⟨⟩
    fromBinary {8} (Vec.take 6 {2} xb Vec.++ Vec.take 2 {4} ((Vec.drop 6 {2} xb) Vec.++ (Vec.take 4 {4} xb₁)))
    ∷ fromBinary {8} (((Vec.drop 2 {4} ((Vec.drop 6 {2} xb) Vec.++ (Vec.take 4 {4} xb₁)))
      Vec.++ (Vec.take 4 {2} (Vec.drop 4 {4} xb₁ Vec.++ Vec.take 2 {6} xb₂))))
    ∷ [ fromBinary {8} (Vec.drop 4 {2} ((Vec.drop 4 {4} xb₁ Vec.++ Vec.take 2 {6} xb₂))
        Vec.++ Vec.drop 2 {6} xb₂) ] ≡⟨⟩
    fromBinary{8} (toBinary{8} x) ∷ fromBinary{8} (toBinary x₁) ∷ [ fromBinary{8} (toBinary x₂) ]
      ≡⟨ cong₂ _∷_
           (fromBinary∘toBinary{8} x)
           (cong₂ (λ x y₁ → x ∷ [ y₁ ])
             (fromBinary∘toBinary{8} x₁)
             (fromBinary∘toBinary{8} x₂)) ⟩
    x ∷ x₁ ∷ [ x₂ ] ∎)

base64To256Valid : (bs : List UInt6) → Valid64Encoding bs → ∃ λ bs' → base64To256 bs ≡ just bs'
base64To256Valid [] v = [] , refl
base64To256Valid (x ∷ x₁ ∷ []) v = _ , refl
base64To256Valid (x ∷ x₁ ∷ x₂ ∷ []) v = _ , refl
base64To256Valid (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ bs) v rewrite (proj₂ (base64To256Valid bs v)) =
  _ , refl

-- encodeValid : ∀ bs → Valid64Encoding (encode bs)
base256To64Valid : (bs : List UInt8) → Valid64Encoding (base256To64 bs)
base256To64Valid [] = tt
base256To64Valid (x ∷ []) = begin
  Vec.drop 2 {4} (toBinary{6} (lookup xs₁ (# 1))) ≡⟨⟩
  Vec.drop 2 {4} (toBinary{6} (fromBinary{6} (lookup (Vec.toList (Bytes.pad256To64₁ (toBinary x))) (# 1))))
    ≡⟨ cong (Vec.drop 2 {4}) (toBinary∘fromBinary{6} (lookup (Vec.toList (Bytes.pad256To64₁ (toBinary x))) (# 1))) ⟩
  Vec.drop 2 {4} (lookup (Vec.toList (Bytes.pad256To64₁ (toBinary x))) (# 1)) ≡⟨⟩
  (Vec.replicate #0 ∎)
  where
  open ≡-Reasoning

  xs₁ : List UInt6
  xs₁ = map (fromBinary{6}) (Vec.toList (Bytes.pad256To64₁ (toBinary x)))
base256To64Valid (x ∷ x₁ ∷ []) = begin
  (Vec.drop 4 {2} (toBinary {6} (lookup xs₁ (# 2))) ≡⟨⟩
  Vec.drop 4 {2} (toBinary {6} (fromBinary{6} (lookup (Vec.toList ((Bytes.pad256To64₂ (toBinary x , toBinary x₁)))) (# 2))))
    ≡⟨ cong (Vec.drop 4 {2}) (toBinary∘fromBinary {6} ((lookup (Vec.toList ((Bytes.pad256To64₂ (toBinary x , toBinary x₁)))) (# 2)))) ⟩
  Vec.drop 4 {2} ((lookup (Vec.toList ((Bytes.pad256To64₂ (toBinary x , toBinary x₁)))) (# 2))) ≡⟨⟩
  Vec.replicate #0 ∎)
  where
  open ≡-Reasoning

  xs₁ : List UInt6
  xs₁ = map fromBinary (Vec.toList (Bytes.pad256To64₂ (toBinary x , toBinary x₁)))
base256To64Valid (x ∷ x₁ ∷ x₂ ∷ bs) = base256To64Valid bs

base256To64∘base64To256 : (bs : List UInt6) → Valid64Encoding bs → maybe (just ∘ base256To64) nothing (base64To256 bs) ≡ just bs
base256To64∘base64To256 [] _ = refl
base256To64∘base64To256 (x ∷ []) ()
base256To64∘base64To256 bs@(x ∷ x₁ ∷ []) v = begin
  maybe{A = List UInt8}{B = const (Maybe (List UInt6))} (just ∘ base256To64) nothing (base64To256 bs) ≡⟨⟩
  (maybe{A = List UInt8}{B = const (Maybe (List UInt6))} (just ∘ base256To64) nothing (just [ y₁ ]) ≡⟨⟩
  (just (base256To64 [ y₁ ]) ≡⟨⟩
  just z ≡⟨ cong just z≡ ⟩
  just bs ∎))
  where
  open ≡-Reasoning

  xb  = toBinary{6} x
  xb₁ = toBinary{6} x₁

  y : List (Binary 8)
  y = Bytes.pad64To256 (Base64.pad2 (xb ∷ Vec.[ xb₁ ]))

  y₁ : UInt8
  y₁ = fromBinary{8} (lookup y (# 0))

  z‼ : Fin 2 → Binary 6
  z‼ = Vec.lookup (Bytes.pad256To64₁ (toBinary y₁))

  z : List UInt6
  z = fromBinary {6} (z‼ (# 0)) ∷ [ fromBinary {6} (z‼ (# 1)) ]

  z≡ : z ≡ bs
  z≡ = begin
    (fromBinary {6} (z‼ (# 0)) ∷ [ fromBinary {6} (z‼ (# 1)) ]
      ≡⟨⟩
    (fromBinary {6} (Vec.take 6 {2} (toBinary y₁))
    ∷ [ fromBinary {6} ((Vec.drop 6 {2} (toBinary y₁)) Vec.++ (Vec.replicate #0)) ]
      ≡⟨⟩
    fromBinary {6} (Vec.take 6 {2} (toBinary{8} (fromBinary{8} (lookup y (# 0)))))
    ∷ [ fromBinary{6} ((Vec.drop 6 {2} (toBinary{8} (fromBinary{8} (lookup y (# 0))))) Vec.++ (Vec.replicate #0)) ]
      ≡⟨ cong₂ (λ x y₂ → x ∷ [ y₂ ])
           (cong (λ x → fromBinary {6} (Vec.take 6 {2} x))
             (toBinary∘fromBinary{8} (lookup y (# 0))))
           (cong (λ x → fromBinary{6} ((Vec.drop 6 {2} x) Vec.++ (Vec.replicate #0)))
             (toBinary∘fromBinary{8} (lookup y (# 0)))) ⟩
    fromBinary {6} (Vec.take 6 {2} (lookup y (# 0)))
    ∷ [ fromBinary {6} ((Vec.drop 6 {2} (lookup y (# 0))) Vec.++ (Vec.replicate #0)) ]
      ≡⟨⟩
    fromBinary {6} (toBinary{6} x)
    ∷ [ fromBinary{6} (Vec.take 2 {4} (toBinary{6} x₁) Vec.++ Vec.replicate #0) ]
      ≡⟨ cong₂ (λ x y₂ → x ∷ [ y₂ ])
        (fromBinary∘toBinary{6} x)
        (begin
          (fromBinary{6} (Vec.take 2 {4} (toBinary{6} x₁) Vec.++ Vec.replicate #0)
            ≡⟨ cong (λ x → fromBinary{6} (Vec.take 2 {4} (toBinary{6} x₁) Vec.++ x))
                 (sym v) ⟩
          fromBinary{6} (toBinary{6} x₁) ≡⟨ fromBinary∘toBinary{6} x₁ ⟩
          x₁ ∎)) ⟩
    x ∷ [ x₁ ] ∎))
base256To64∘base64To256 bs@(x ∷ x₁ ∷ x₂ ∷ []) v = begin
  (maybe {A = List UInt8} {B = const (Maybe (List UInt6))} (just ∘ base256To64) nothing
    (base64To256 bs) ≡⟨⟩
  (maybe {A = List UInt8} {B = const (Maybe (List UInt6))} (just ∘ base256To64) nothing
    (just (y₁ ∷ [ y₂ ])) ≡⟨⟩
  (just (base256To64 (y₁ ∷ [ y₂ ])) ≡⟨⟩
  just z ≡⟨ cong just z≡ ⟩
  just bs ∎)))
  where
  open ≡-Reasoning

  bs' : Vec (Binary 6) 3
  bs' = Vec.map (toBinary{6}) (x ∷ x₁ ∷ Vec.[ x₂ ])

  ys' : List (Binary 8)
  ys' = Bytes.pad64To256 (Base64.pad1 bs')

  ys : List UInt8
  ys = map (fromBinary {8}) ys'

  y₁ y₂ : UInt8
  y₁ = lookup ys (# 0)
  y₂ = lookup ys (# 1)

  z' = Vec.toList (Bytes.pad256To64₂ (toBinary y₁ , toBinary y₂))

  z : List UInt6
  z = map (fromBinary {6}) z'

  z≡ : z ≡ bs
  z≡ = begin
    (  fromBinary{6} (lookup z' (# 0))
     ∷ fromBinary{6} (lookup z' (# 1))
     ∷ [ fromBinary{6} (lookup z' (# 2)) ] ≡⟨⟩
    (fromBinary {6} (Vec.take 6 {2} (toBinary y₁))
     ∷ fromBinary{6} ((Vec.drop 6 {2} (toBinary y₁)) Vec.++ (Vec.take 4 {4} (toBinary y₂)))
     ∷ [ fromBinary {6} ((Vec.drop 4 {4} (toBinary y₂)) Vec.++ (Vec.replicate #0)) ] ≡⟨⟩
    fromBinary{6} (Vec.take 6 {2} (toBinary{8} (fromBinary{8} (lookup ys' (# 0)))))
    ∷ fromBinary{6} (Vec.drop 6 {2} (toBinary{8} (fromBinary{8} (lookup ys' (# 0))))
      Vec.++ Vec.take 4 {4} (toBinary{8} (fromBinary{8} (lookup ys' (# 1)))))
    ∷ [ fromBinary{6} (Vec.drop 4 {4} (toBinary{8} (fromBinary{8} (lookup ys' (# 1))))
        Vec.++ Vec.replicate #0) ]
    ≡⟨ cong₂ _∷_
         (cong (λ x → fromBinary{6} (Vec.take 6 {2} x))
           (toBinary∘fromBinary{8} (lookup ys' (# 0))))
         (cong₂ (λ x y → x ∷ [ y ])
           (cong₂ (λ x y → fromBinary {6} ((Vec.drop 6 {2} x) Vec.++ (Vec.take 4 {4} y)))
             (toBinary∘fromBinary {8} (lookup ys' (# 0)))
             (toBinary∘fromBinary {8} (lookup ys' (# 1))))
           (cong
             (λ x → fromBinary{6} ((Vec.drop 4 {4} x) Vec.++ Vec.replicate #0))
             (toBinary∘fromBinary{8} (lookup ys' (# 1))))) ⟩
    fromBinary {6} (Vec.take 6 {2} (lookup ys' (# 0)))
    ∷ fromBinary {6}
        (Vec.drop 6 {2} (lookup ys' (# 0))
         Vec.++ Vec.take 4 {4} (lookup ys' (# 1)))
    ∷ [ fromBinary {6}
          (Vec.drop 4 {4} (lookup ys' (# 1))
           Vec.++ Vec.replicate #0) ] ≡⟨⟩
    (fromBinary {6} (toBinary{6} x)
    ∷ fromBinary{6} (toBinary{6} x₁)
    ∷ [ fromBinary{6}
          (Vec.take 4 {2} (toBinary{6} x₂) Vec.++ Vec.replicate #0) ]
    ≡⟨ cong₂ _∷_ (fromBinary∘toBinary{6} x)
       (cong₂ (λ x y → x ∷ [ y ])
         (fromBinary∘toBinary{6} x₁)
         (begin
           (fromBinary{6} (Vec.take 4 {2} (toBinary{6} x₂) Vec.++ Vec.replicate #0)
           ≡⟨ cong (λ x → fromBinary{6} (Vec.take 4 {2} (toBinary{6} x₂) Vec.++ x))
                (sym v) ⟩
           fromBinary{6} (toBinary{6} x₂) ≡⟨ fromBinary∘toBinary{6} x₂ ⟩
           x₂ ∎))) ⟩
    bs ∎)))
base256To64∘base64To256 xs@(x ∷ x₁ ∷ x₂ ∷ x₃ ∷ bs) v = begin
  (maybe {A = List UInt8}{B = const (Maybe (List UInt6))}
    (just ∘ base256To64) nothing
    (base64To256 (Vec.toList bs' ++ bs)) ≡⟨⟩
  (maybe {A = List UInt8}{B = const (Maybe (List UInt6))}
    (just ∘ base256To64) nothing
    (maybe{A = List UInt8}{B = const (Maybe (List UInt8))}
      (λ ds → just (Vec.toList ys' ++ ds)) nothing
      (base64To256 bs))
  ≡⟨ cong
       (λ x →
         maybe {A = List UInt8}{B = const (Maybe (List UInt6))}
           (just ∘ base256To64) nothing
           (maybe{A = List UInt8}{B = const (Maybe (List UInt8))}
             (λ ds → just (Vec.toList ys' ++ ds)) nothing x))
             (proj₂ lem) ⟩
  just (base256To64 (Vec.toList ys' ++ ys“)) ≡⟨⟩
  just (zs' ++ base256To64 ys“) ≡⟨⟩
  Maybe.map (zs' ++_)
    (maybe′ (just ∘ base256To64) nothing (just ys“))
  ≡⟨ cong (λ x → Maybe.map (zs' ++_) (maybe (just ∘ base256To64) nothing x))
       (sym (proj₂ lem)) ⟩
  Maybe.map (zs' ++_)
    (maybe′ (just ∘ base256To64) nothing (base64To256 bs))
      ≡⟨ cong (Maybe.map (zs' ++_))
           (base256To64∘base64To256 bs v) ⟩
  just (zs' ++ bs) ≡⟨ cong (λ x → just (x ++ bs)) zs'≡ ⟩
  just xs ∎))
  where
  open ≡-Reasoning

  bs' : Vec UInt6 4
  bs' = x ∷ x₁ ∷ x₂ ∷ Vec.[ x₃ ]

  bs“ : Vec (Binary 6) 4
  bs“ = Vec.map (toBinary{6}) bs'

  ys  = Bytes.base64To256 bs“
  ys' = Vec.map fromBinary ys

  lem = base64To256Valid bs v
  ys“ = proj₁ lem

  ys‴ = Vec.map toBinary ys'
  zs = Bytes.base256To64 ys‴
  
  zs' = map fromBinary (Vec.toList zs)

  zs'≡ : zs' ≡ Vec.toList bs'
  zs'≡ = begin
    (fromBinary {6} (Vec.take 6 {2} (Vec.lookup ys‴ (# 0)))
    ∷ fromBinary{6} ((Vec.drop 6 {2} (Vec.lookup ys‴ (# 0))) Vec.++ (Vec.take 4 {4} (Vec.lookup ys‴ (# 1))))
    ∷ fromBinary {6} ((Vec.drop 4 {4} (Vec.lookup ys‴ (# 1))) Vec.++ (Vec.take 2 {6} (Vec.lookup ys‴ (# 2))))
    ∷ [ fromBinary {6} (Vec.drop 2 {6} (Vec.lookup ys‴ (# 2))) ] ≡⟨⟩

    fromBinary {6} (Vec.take 6 {2} (toBinary{8} (fromBinary {8} (Vec.lookup ys (# 0)))))
    ∷ fromBinary{6}
               ((Vec.drop 6 {2} ((toBinary{8} (fromBinary {8} (Vec.lookup ys (# 0))))))
        Vec.++ (Vec.take 4 {4} (toBinary{8} (fromBinary{8} (Vec.lookup ys (# 1))))))
    ∷ fromBinary {6}
               ((Vec.drop 4 {4} (toBinary {8} (fromBinary{8} (Vec.lookup ys (# 1)))))
        Vec.++ (Vec.take 2 {6} (toBinary{8} (fromBinary{8} (Vec.lookup ys (# 2))))))
    ∷ [ fromBinary {6} (Vec.drop 2 {6} (toBinary{8} (fromBinary{8} (Vec.lookup ys (# 2))))) ]
    ≡⟨ cong₂ _∷_
         (cong (λ x → fromBinary{6} (Vec.take 6 {2} x))
           (toBinary∘fromBinary {8} (Vec.lookup ys (# 0))))
         (cong₂ _∷_
           (cong₂ (λ x y → fromBinary{6} (Vec.drop 6 {2} x Vec.++ Vec.take 4 {4} y))
             (toBinary∘fromBinary{8} (Vec.lookup ys (# 0)))
             (toBinary∘fromBinary{8} (Vec.lookup ys (# 1))))
           (cong₂ (λ x y → x ∷ [ y ])
             (cong₂ (λ x y → fromBinary{6} ((Vec.drop 4 {4} x) Vec.++ (Vec.take 2 {6} y)))
               (toBinary∘fromBinary{8} (Vec.lookup ys (# 1)))
               (toBinary∘fromBinary{8} (Vec.lookup ys (# 2))))
             (cong (λ x → fromBinary {6} (Vec.drop 2 {6} x))
               (toBinary∘fromBinary{8} (Vec.lookup ys (# 2)))))) ⟩

    fromBinary{6} (toBinary{6} x)
    ∷ fromBinary{6} (toBinary{6} x₁)
    ∷ fromBinary {6} (toBinary{6} x₂)
    ∷ [ fromBinary{6} (toBinary{6} x₃) ]
    ≡⟨ cong₂ _∷_ (fromBinary∘toBinary{6} x)
       (cong₂ _∷_ (fromBinary∘toBinary{6} x₁)
       (cong₂ (λ x y → x ∷ [ y ])
         (fromBinary∘toBinary{6} x₂)
         (fromBinary∘toBinary{6} x₃))) ⟩

    x ∷ x₁ ∷ x₂ ∷ [ x₃ ] ∎)
