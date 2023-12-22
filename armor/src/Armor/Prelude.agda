module Armor.Prelude where

module Level where
  open import Level public

open import Data.Bool    public
  hiding (_<_ ; _<?_ ; _≟_ ; _≤_ ; _≤?_)

open import Data.Empty public
  hiding (⊥-elim)

⊥-elim : ∀ {ℓ} {@0 A : Set ℓ} → @0 ⊥ → A
⊥-elim ()

⊥-irrel : (@0 _ : ⊥) → ⊥
⊥-irrel ()

import Data.Char
module Char = Data.Char
Char = Char.Char

import Data.Fin
module Fin where
  open Data.Fin public

  open import Data.Nat
    renaming (_+_ to _+ℕ_ ; pred to predℕ)
  open import Data.Nat.Properties
  open import Relation.Binary.PropositionalEquality

  2*_ : ∀ {m} → Fin m → Fin (predℕ (2 * m))
  2* (zero{n}) = subst Fin (sym (+-suc n (n +ℕ 0))) zero
  2* (suc{suc n} i) = subst Fin (cong suc (sym (+-suc n (suc (n +ℕ 0))))) (suc (suc (2* i)))

  open import Data.Fin.Properties public

Fin = Fin.Fin

import Data.Integer
module ℤ = Data.Integer
ℤ = ℤ.ℤ

module List where
  open import Data.List    public
    hiding (_─_)

  open import Data.List.Relation.Unary.Unique.DecPropositional public
    using (Unique ; unique?)

  open import Data.List.Relation.Unary.AllPairs public
    using (AllPairs ; [] ; _∷_)
open List public hiding (Unique ; unique? ; module List)

open import Data.List.Properties public

module All where
  open import Data.List.Relation.Unary.All
    public
    hiding (module All)
  open import Data.List.Relation.Unary.All.Properties public
open All public using (All ; [] ; _∷_)

open import Data.List.Relation.Unary.Any public
  using (here ; there)
module Any where
  open import Data.List.Relation.Unary.Any            public
  open import Data.List.Relation.Unary.Any.Properties public
Any = Any.Any

open import Data.List.Membership.Propositional public
  using (_∈_ ; _∉_)

import Data.List.Membership.DecPropositional

-- import Data.Maybe
-- module Maybe = Data.Maybe
-- open Data.Maybe public
--   hiding (align ; alignWith ; fromMaybe ; map ; zip ; zipWith ; _>>=_)

import Data.Maybe
module Maybe where
  open Data.Maybe public
open Maybe public
  hiding (module Maybe ; align ; alignWith ; fromMaybe ; map ; zip ; zipWith ; _>>=_)

open import Data.Nat     public
  hiding (_≟_)
open import Data.Nat.DivMod public
open import Agda.Builtin.Nat public
  using (_-_)

headSafe : ∀ {ℓ} {@0 A : Set ℓ} → (xs : List A) → @0 length xs ≥ 1 → A
headSafe (x₁ ∷ xs) x = x₁

tailSafe : ∀ {ℓ} {@0 A : Set ℓ} → (xs : List A) → @0 length xs ≥ 1 → List A
tailSafe (_ ∷ xs) _ = xs

open import Data.Product public
  hiding (map ; zip)

infixr 4 _,e_
_,e_ : ∀ {ℓ₁ ℓ₂} {@0 A : Set ℓ₁}{@0 B : A → Set ℓ₂} → (a : A) (b : B a) → Σ A B
proj₁ (a ,e b) = a
proj₂ (a ,e b) = b

infixr 4 _,′e_
_,′e_ : ∀ {ℓ₁ ℓ₂} {@0 A : Set ℓ₁} {@0 B : Set ℓ₂} → (a : A) (b : B) → A × B
proj₁ (a ,′e b) = a
proj₂ (a ,′e b) = b

proj₁₀ : ∀ {ℓ₁ ℓ₂} {@0 A : Set ℓ₁} {@0 B : A → Set ℓ₂} → Σ A B → A
proj₁₀ (a , b) = a

proj₂₀ : ∀ {ℓ₁ ℓ₂} {@0 A : Set ℓ₁} {@0 B : A → Set ℓ₂} → (x : Σ A B) → B (proj₁₀ x)
proj₂₀ (a , b) = b

import Data.String
module String where
  open Data.String public
  open import Agda.Builtin.String public
    using ()
    renaming (primShowNat to showNat)
String = String.String

open import Data.Sum     public
  hiding (map ; map₁ ; map₂ ; swap ; assocʳ ; assocˡ)

open import Data.Unit    public
  using (⊤ ; tt)

open import Data.Vec public
  using (_∷_ ; [])
module Vec = Data.Vec
Vec = Vec.Vec

open import Function     public
  hiding (_∋_ ; it)

it : ∀ {ℓ} {@0 A : Set ℓ} → ⦃ A ⦄ → A
it ⦃ x ⦄ = x


infix  0 case_ret_of_
infix  0 caseErased_ret_of_
infixl 0 _∋_

case_ret_of_ : ∀ {ℓ₁ ℓ₂} {@0 A : Set ℓ₁}
               → (x : A) (@0 B : A → Set ℓ₂)
               → ((x : A) → B x) → B x
case a ret B of f = f a

_∋_ : ∀ {ℓ} (@0 A : Set ℓ) → A → A
A ∋ a = a

import Induction.WellFounded
module WellFounded where
  open Induction.WellFounded public
Acc = WellFounded.Acc


open import Relation.Binary public
  using ()
  renaming (Irrelevant to Unique₂ ; Decidable to Decidable₂)

open import Relation.Binary.PropositionalEquality public
  hiding (decSetoid ; cong)
  renaming ([_] to [_]R)
module Reveal = Reveal_·_is_

≡-unique : ∀ {ℓ} {@0 A : Set ℓ} → Unique₂ (_≡_{A = A})
≡-unique refl refl = refl

≡-irrel : ∀ {ℓ} {A : Set ℓ} {x y : A} → (@0 _ : x ≡ y) → x ≡ y
≡-irrel refl = refl

≡-elim : ∀ {ℓ ℓ₁}{A : Set ℓ}{x : A} →
         (@0 P : ∀ {y} → x ≡ y → Set ℓ₁) →
         P refl → ∀ {y} (eq : x ≡ y) → P eq
≡-elim P pf refl = pf

≡-elimₖ : ∀ {ℓ ℓ₁}{A : Set ℓ}{x : A} →
          (@0 P : x ≡ x → Set ℓ₁) →
          P refl → (eq : x ≡ x) → P eq
≡-elimₖ P pf refl = pf

cong : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) {@0 x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl


subst₀ : ∀ {ℓ₁ ℓ₂} {@0 A : Set ℓ₁} (@0 P : A → Set ℓ₂) {@0 x y : A} → (@0 _ : x ≡ y) → P x → P y
subst₀ P refl x = x

subst₀! : ∀ {ℓ₁ ℓ₂} {@0 A : Set ℓ₁} (@0 P : @0 A → Set ℓ₂) {@0 x y : A} → (@0 _ : x ≡ y) → P x → P y
subst₀! P refl x = x

transp : ∀ {ℓ₁ ℓ₂} {@0 A : Set ℓ₁} {@0 B : A → Set ℓ₂} (f : (a : A) → B a)
         → {@0 x y : A} (eq : x ≡ y) → subst B eq (f x) ≡ f y
transp f refl = refl

trans₀ : ∀ {ℓ} {@0 A : Set ℓ} {@0 x y z : A} → (@0 _ : x ≡ y) (@0 _ : y ≡ z) → x ≡ z
trans₀ refl refl = refl

≤-unique : Unique₂ _≤_
≤-unique = ≤-irrelevant
  where open import Data.Nat.Properties

open import Relation.Binary.Definitions public
  using (Tri ; tri< ; tri≈ ; tri> )

open import Relation.Nullary public
  renaming (Irrelevant to Unique)

yes₀ : ∀ {ℓ} {@0 P : Set ℓ} → P → Dec P
yes₀ p = true because (ofʸ p)

no₀ : ∀ {ℓ} {@0 P : Set ℓ} → ¬ P → Dec P
no₀ p = false because (ofⁿ p)

⊤-unique : Unique ⊤
⊤-unique tt tt = refl

×-unique : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → Unique A → Unique B → Unique (A × B)
×-unique ua ub (a , b) (c , d)
  with ua a c
  |    ub b d
... | refl | refl = refl

⊎-unique : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → Unique A → Unique B → ¬ (A × B) → Unique (A ⊎ B)
⊎-unique uA uB ¬A×B (inj₁ x) (inj₁ x₁) = cong inj₁ (uA x x₁)
⊎-unique uA uB ¬A×B (inj₁ x) (inj₂ y) = ⊥-elim (¬A×B (x , y))
⊎-unique uA uB ¬A×B (inj₂ y) (inj₁ x) = ⊥-elim (¬A×B (x , y))
⊎-unique uA uB ¬A×B (inj₂ y) (inj₂ y₁) = cong inj₂ (uB y y₁)

open import Relation.Nullary.Negation public
  hiding (contradiction ; contraposition)

contradiction : ∀ {ℓ ℓ'} {@0 P : Set ℓ} {@0 A : Set ℓ'} → @0 P → @0 ¬ P → A
contradiction p ¬p = ⊥-elim (¬p p)

contraposition : ∀ {ℓ₁ ℓ₂} {@0 P : Set ℓ₁} {@0 Q : Set ℓ₂} → (P → Q) → ¬ Q → ¬ P
contraposition p⇒q ¬q p = contradiction (p⇒q p) ¬q

open import Relation.Nullary.Decidable public
  hiding (map)

T-unique : ∀ {b} → Unique (T b)
T-unique {true} tt tt = refl

T-dec : ∀ {b} → Dec (T b)
T-dec {false} = no λ ()
T-dec {true} = yes tt

True_And_ : ∀ {ℓ₁ ℓ₂} {P : Set ℓ₁} → Dec P → (P → Set ℓ₂) → Set ℓ₂
True_And_ (yes pf) Q = Q pf
True_And_{ℓ₂ = ℓ₂} (no ¬pf) Q = Level.Lift ℓ₂ ⊥

open import Relation.Nullary.Product public
  using (_×-dec_)

open import Relation.Nullary.Sum public
  using (_⊎-dec_)

open import Relation.Unary public
  using (Decidable)
  renaming (Irrelevant to Unique₁)

-- Definitions
infixl 7 _%2^_
_%2^_ : (m n : ℕ) → ℕ
m %2^ n = _%_ m (2 ^ n) {fromWitnessFalse {Q = 2 ^ n Data.Nat.≟ 0} (λ eq → case 2 ≡ 0 ∋ m^n≡0⇒m≡0 2 n eq of λ ())}
  where open import Data.Nat.Properties


record Singleton {ℓ} {@0 A : Set ℓ} (@0 a : A) : Set ℓ where
  constructor singleton
  field
    x : A
    @0 x≡ : x ≡ a

↑_ = Singleton.x

pattern self {a} = singleton a refl

singleSelf : ∀ {ℓ} {@0 A : Set ℓ} → {a : A} → Singleton a
singleSelf{a = a} = singleton a refl

uniqueSingleton : ∀ {ℓ} {@0 A : Set ℓ} {a : A} → Unique (Singleton a)
uniqueSingleton self self = refl

mapSingleton : ∀ {ℓ₁ ℓ₂} {@0 A : Set ℓ₁} {@0 B : Set ℓ₂}
               → (f : A → B) {@0 a : A}
               → Singleton a → Singleton (f a)
mapSingleton f (singleton x x≡) = singleton (f x) (cong f x≡)

infix 100 ─_
record Erased {ℓ} (@0 A : Set ℓ) : Set ℓ where
  constructor ─_
  field
    @0 x : A

infix 100 ¡_
@0 ¡_ : _
¡_ = Erased.x

erasedEta : ∀ {ℓ} {@0 A : Set ℓ} (x : Erased A)
            → x ≡ ─ Erased.x x
erasedEta (─ x) = refl

@0 caseErased_ret_of_ : ∀ {ℓ₁ ℓ₂} {@0 A : Set ℓ₁}
                        → (x : A) (@0 B : A → Set ℓ₂)
                        → ((x : A) → Erased (B x)) → B x
caseErased x ret _ of f = ¡ f x

erased? : ∀ {ℓ} {@0 A : Set ℓ} → Dec A → Dec (Erased A)
erased? (no ¬a) = no λ where
  (─ x) → contradiction x ¬a
erased? (yes a) = yes (─ a)

uneraseDec : ∀ {ℓ} {@0 A : Set ℓ} → @0 A → Dec A → A
uneraseDec{A = A} x (no ¬p) = contradiction{A = A} x ¬p 
uneraseDec x (yes p) = p

erased-unique : ∀ {ℓ} {@0 A : Set ℓ} → Unique A → Unique (Erased A)
erased-unique u (─ x) (─ y) = subst₀ (λ y → ─ x ≡ ─ y) (u x y) refl

@0 liftMapErase : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → Erased B) → List A → List B
liftMapErase f [] = []
liftMapErase f (x ∷ xs) = (¡ f x) ∷ liftMapErase f xs

Exists─ : (@0 A : Set) (B : @0 A → Set) → Set
Exists─ A B = Σ[ x ∈ Erased A ] let (─ y) = x in B y

curry─ : {A : Set} {B : @0 A → Set} {C : Exists─ A B → Set}
         → ((p : Exists─ A B) → C p)
         → {@0 x : A} (y : B x) → C (─ x , y)
curry─ p y = p (─ _ , y)


uncurry─ : {A : Set} {B : @0 A → Set} {C : Exists─ A B → Set}
           → ({@0 x : A} (y : B x) → C (─ x , y))
           → (e : Exists─ A B) → C e
uncurry─ f (─ fst , snd) = f {fst} snd

-- Typeclasses

record Numeric {ℓ} (A : Set ℓ) : Set ℓ where
  field
    toℕ : A → ℕ
open Numeric ⦃ ... ⦄ public

infix 10 #_
#_ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Numeric A ⦄
     → (m : A) {n : ℕ} {m<n : True (suc (toℕ m) ≤? n) } → Fin n
#_ _ {m<n = m<n} = Fin.fromℕ< (toWitness m<n)

InRange : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} ⦃ _ : Numeric A ⦄ ⦃ _ : Numeric B ⦄
          → (l u : A) → B → Set
InRange l u x = toℕ l ≤ toℕ x × toℕ x ≤ toℕ u

inRange? : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} ⦃ _ : Numeric A ⦄ ⦃ _ : Numeric B ⦄
          → (l u : A)
          → (x : B) → Dec (InRange l u x)
inRange? l u x = toℕ l ≤? toℕ x ×-dec toℕ x ≤? toℕ u

inRange-unique : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} ⦃ _ : Numeric A ⦄ ⦃ _ : Numeric B ⦄
                 → ∀ {l u : A} {x : B}
                 → (pf₁ pf₂ : InRange l u x) → pf₁ ≡ pf₂
inRange-unique = ×-unique ≤-irrelevant ≤-irrelevant
  where open import Data.Nat.Properties

inRange-relax
  : ∀ {ℓ₁ ℓ₂} {@0 A : Set ℓ₁} {B : Set ℓ₂} ⦃ _ : Numeric A ⦄ ⦃ _ : Numeric B ⦄
    → ∀ {l l' u u' : A} {x : B}
    → (pf : InRange l u x) → toℕ l' ≤ toℕ l → toℕ u ≤ toℕ u'
    → InRange l' u' x
inRange-relax pf l'≤l u≤u' = ≤-trans l'≤l (proj₁ pf) , ≤-trans (proj₂ pf) u≤u'
  where open import Data.Nat.Properties

instance
  ℕNumeric : Numeric ℕ
  Numeric.toℕ ℕNumeric = id

  BoolNumeric : Numeric Bool
  Numeric.toℕ BoolNumeric false = 0
  Numeric.toℕ BoolNumeric true = 1

  FinNumeric : ∀ {n} → Numeric (Fin n)
  Numeric.toℕ FinNumeric = Fin.toℕ

  CharNumeric : Numeric Char
  Numeric.toℕ CharNumeric = Char.toℕ

  SingletonNumeric : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Numeric A ⦄ {@0 x : A} → Numeric (Singleton x)
  Numeric.toℕ SingletonNumeric = toℕ ∘ Singleton.x

record Eq {ℓ} (@0 A : Set ℓ) : Set ℓ where
  infix 4 _≟_ _≠_
  field
    _≟_ : (x y : A) → Dec (x ≡ y)

  _≠_ : (x y : A) → Dec (x ≢ y)
  x ≠ y
    with x ≟ y
  ... | no  ≠  = yes ≠
  ... | yes pf = no λ ≢ → ≢ pf

open Eq ⦃ ... ⦄ public

infix 4 _∈?_ _∉?_

_∈?_ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Eq A ⦄ → ∀ (x : A) xs → Dec (x ∈ xs)
_∈?_ = Data.List.Membership.DecPropositional._∈?_ _≟_

_∉?_ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Eq A ⦄ → ∀ (x : A) xs → Dec (x ∉ xs)
_∉?_ = Data.List.Membership.DecPropositional._∉?_ _≟_

unique? : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Eq A ⦄ → ∀ xs → Dec (List.Unique _≟_ xs)
unique? = List.unique? _≟_

∈-unique : ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} ⦃ _ : Eq A ⦄
           → List.Unique _≟_ xs → (x∈₁ x∈₂ : x ∈ xs) → x∈₁ ≡ x∈₂
∈-unique _ (here refl) (here refl) = refl
∈-unique (d ∷ u) (here refl) (there x∈₂) =
  contradiction x∈₂ (All.All¬⇒¬Any d)
∈-unique (d ∷ u) (there x∈₁) (here refl) =
  contradiction x∈₁ (All.All¬⇒¬Any d)
∈-unique (d ∷ u) (there x∈₁) (there x∈₂) =
  cong (Any.there) (∈-unique u x∈₁ x∈₂)

instance
  ℕEq : Eq ℕ
  Eq._≟_ ℕEq = Data.Nat._≟_

  CharEq : Eq Char
  Eq._≟_ CharEq = Char._≟_

  FinEq : ∀ {n} → Eq (Fin n)
  Eq._≟_ FinEq = Fin._≟_

  ℤEq : Eq ℤ
  Eq._≟_ ℤEq = ℤ._≟_

  ListEq : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Eq A ⦄ → Eq (List A)
  Eq._≟_ ListEq = ≡-dec _≟_

  BoolEq : Eq Bool
  Eq._≟_ BoolEq = Data.Bool._≟_

  SingletonEq : ∀ {ℓ} {@0 A : Set ℓ} → {@0 a : A} → Eq (Singleton a)
  Eq._≟_ SingletonEq self self = yes refl

record Show {ℓ} (@0 A : Set ℓ) : Set ℓ where
  field
    show : A → String
open Show ⦃ ... ⦄ public

instance
  showNat : Show ℕ
  Show.show showNat = Nat.show
    where import Data.Nat.Show as Nat

  showList : ∀ {ℓ} {@0 A : Set ℓ} ⦃ _ : Show A ⦄ → Show (List A)
  Show.show (showList{A = A}) xs = "[ " String.++ help xs String.++ " ]"
    where
    help : (xs : List A) → String
    help [] = ""
    help (x ∷ []) = show x String.++ " "
    help (x ∷ xs) = show x String.++ " , " String.++ help xs

record Irrel {ℓ} (@0 A : Set ℓ) : Set ℓ where
  infix 10 ‼_
  field
    irrel : (@0 _ : A) → A
  ‼_ = irrel
open Irrel ⦃ ... ⦄ public
infix 10 ̂‼_
̂‼_ : ∀ {ℓ} {@0 A : Set ℓ} → ⦃ _ : Irrel A ⦄ → Erased A → A
̂‼ (─ x) = ‼ x

instance
  IrrelBot : Irrel ⊥
  Irrel.irrel IrrelBot = ⊥-irrel

  Irrel≡ : ∀ {ℓ} {@0 A : Set ℓ} {@0 x y : A} → Irrel (x ≡ y)
  Irrel.irrel Irrel≡ refl = refl

  Irrel¬ : ∀ {ℓ} {A : Set ℓ} → Irrel (¬ A)
  Irrel.irrel Irrel¬ ¬a a = contradiction a ¬a

import Category.Monad
Monad = Category.Monad.RawMonad
MonadZero = Category.Monad.RawMonadZero

module Monad {ℓ} {M : Set ℓ → Set ℓ} (m : Monad M) where
  open Category.Monad.RawMonad m public
    hiding (zip ; zipWith)

open Monad ⦃ ... ⦄ public

instance
  MonadMaybe : ∀ {ℓ} → Monad{ℓ} Maybe
  MonadMaybe = monad
    where open import Data.Maybe.Categorical

  MonadError : ∀ {ℓ₁ ℓ₂} {E : Set ℓ₁} → Monad{ℓ₁ Level.⊔ ℓ₂} (E ⊎_)
  MonadError{ℓ₂ = ℓ₂}{E = E} = monad
    where open import Data.Sum.Categorical.Left E ℓ₂

module MonadZero {ℓ} {M : Set ℓ → Set ℓ} (m : MonadZero M) where
  import Category.Monad

  ∅ = Category.Monad.RawMonadZero.∅ m

open MonadZero ⦃ ... ⦄ public

instance
  MonadZeroMaybe : ∀ {ℓ} → MonadZero{ℓ} Maybe
  MonadZeroMaybe = monadZero
    where open import Data.Maybe.Categorical

record Writer {ℓ} (M : Set ℓ → Set ℓ) (W : Set ℓ) : Set ℓ where
  field
    tell : W → M (Level.Lift _ ⊤)

open Writer ⦃ ... ⦄ public

record Logging {ℓ} (A : Set ℓ) : Set ℓ where
  constructor mkLogged
  field
    log : List String.String
    val : A

instance
  MonadLogging : ∀ {ℓ} → Monad{ℓ} Logging
  Monad.return MonadLogging x = mkLogged [] x
  Monad._>>=_  MonadLogging (mkLogged log₁ val₁) f
    with f val₁
  ... | mkLogged log₂ val₂ = mkLogged (log₁ ++ log₂) val₂

  WriterLogging : Writer Logging String.String
  Writer.tell   WriterLogging w = mkLogged [ w String.++ "\n" ] (Level.lift tt)

silent : ∀{ℓ} → Logging (Level.Lift ℓ ⊤)
silent = return (Level.lift tt)

-- Lemmas
module Lemmas where

  open import Tactic.MonoidSolver using (solve ; solve-macro)
  open import Data.Nat.Properties
  import      Data.Integer.Properties as ℤ
  open import Data.List.Properties
  import      Data.Sign as Sign

  -- TODO remove this, in the standard library already as m+[n∸m]≡n
  m+n-m≡n : ∀ {m n} → m ≤ n → m + (n - m) ≡ n
  m+n-m≡n{m}{n} m≤n = begin
    m + (n - m) ≡⟨ sym $ +-∸-assoc m m≤n ⟩
    m + n - m ≡⟨ cong (_∸ m) (+-comm m n) ⟩
    n + m - m ≡⟨ +-∸-assoc n {m} ≤-refl ⟩
    n + (m - m) ≡⟨ cong (n +_) (n∸n≡0 m) ⟩
    n + 0 ≡⟨ +-identityʳ n ⟩
    n ∎
    where open ≡-Reasoning

  ++-assoc₄ : ∀ {ℓ} {A : Set ℓ} (ws xs ys zs : List A) → ws ++ xs ++ ys ++ zs ≡ (ws ++ xs ++ ys) ++ zs
  ++-assoc₄{A = A} ws xs ys zs = solve (++-monoid A)

  m*n≡[suc-m]*n∸n : ∀ m n → (n > 0) → m * n ≡ suc m * n - n
  m*n≡[suc-m]*n∸n zero n n>0 =
    (begin
      0 ≡⟨ sym (n∸n≡0 n) ⟩
      n - n ≡⟨ cong (_∸ n) (sym (+-identityʳ n)) ⟩
      (n + 0) - n ∎)
    where
    open ≡-Reasoning
  m*n≡[suc-m]*n∸n (suc m) n n>0 =
    n + (m * n) ≡⟨ cong (n +_) ih ⟩
    n + (n + m * n - n) ≡⟨ sym (+-∸-assoc n (n ≤ n + m * n ∋ m≤m+n _ _)) ⟩
    n + (n + m * n) - n ∎
    where
    open ≡-Reasoning

    ih : m * n ≡ n + m * n - n
    ih = m*n≡[suc-m]*n∸n m n n>0

  m^n≥1 : ∀ m n → m > 0 → m ^ n ≥ 1
  m^n≥1 m zero x = ≤-refl
  m^n≥1 m (suc n) x =
    ≤.begin
      1 ≤.≤⟨ x ⟩
      m ≤.≤⟨ m≤m*n m (m^n≥1 m n x) ⟩
      m * (m ^ n) ≤.∎
    where
    module ≤ = ≤-Reasoning

  ^-monoʳ-≤ : ∀ m {n o} → m > 0 → n ≤ o → m ^ n ≤ m ^ o
  ^-monoʳ-≤ m{o = o} m>0 z≤n = m^n≥1 m o m>0
  ^-monoʳ-≤ m{n}{o} m>0 (s≤s x) = *-monoʳ-≤ m (^-monoʳ-≤ m m>0 x)

  m≤n⇒∃[o]o+m≡n : ∀ {m n} → m ≤ n → ∃ λ o → o + m ≡ n
  m≤n⇒∃[o]o+m≡n {.zero} {n} z≤n = _ , (+-identityʳ n)
  m≤n⇒∃[o]o+m≡n {.(suc _)} {.(suc _)} (s≤s m≤n)
    with m≤n⇒∃[o]o+m≡n m≤n
  ... | (o , o+m≡n) = o , trans (+-suc o _) (cong suc o+m≡n)

  -- DivMod properties in terms of _div_, _mod_, and _divMod_
  m%n<n' : ∀ m n {≢0 : False (n Data.Nat.≟ 0)} → (m % n) {≢0} < n
  m%n<n' m (suc n) = m%n<n m n

  m*n%n≡0-mod : ∀ m n {≢0 : False (n Data.Nat.≟ 0)} → (m * n % n){≢0} ≡ 0
  m*n%n≡0-mod m (suc n) = m*n%n≡0 m n

  m≤n⇒m%n≡m-mod : ∀ {m n} {≢0 : False (n Data.Nat.≟ 0)} → m < n → toℕ ((m mod n){≢0}) ≡ m
  m≤n⇒m%n≡m-mod {m} {suc n} {≢0} (s≤s m<n) = begin
    Fin.toℕ (Fin.fromℕ< (m%n<n m n)) ≡⟨ Fin.toℕ-fromℕ< (m%n<n m n) ⟩
    m % (suc n) ≡⟨ m≤n⇒m%n≡m m<n ⟩
    m ∎
    where
    open ≡-Reasoning

  m≤n⇒m%n≡m-mod' : ∀ {m n} {≢0 : False (n Data.Nat.≟ 0)} → m < n → (m % n){≢0} ≡ m
  m≤n⇒m%n≡m-mod' {m} {suc n} {≢0} (s≤s m<n) = m≤n⇒m%n≡m m<n

  [m+kn]%n≡m%n-divMod : ∀ m k n {≢0 : False (n Data.Nat.≟ 0)}
                        → let (result q r _) = ((m + k * n) divMod n){≢0} in
                          r ≡ (m mod n){≢0}
  [m+kn]%n≡m%n-divMod m k (suc n) =
    Fin.toℕ-injective (begin
      toℕ (Fin.fromℕ< (m%n<n (m + k * (suc n)) n)) ≡⟨ Fin.toℕ-fromℕ< (m%n<n (m + k * (suc n)) n) ⟩
      (m + k * (suc n)) % (suc n) ≡⟨ [m+kn]%n≡m%n m k n ⟩
      m % (suc n) ≡⟨ sym (Fin.toℕ-fromℕ< (m%n<n m n)) ⟩
      toℕ (m mod (suc n)) ∎)
    where
    open ≡-Reasoning

  +-distrib-/-divMod
    : ∀ m n {d} {≢0} →
      let (result q r _) = ((m + n) divMod d){≢0} in
      (m % d){≢0} + (n % d){≢0} < d
      → q ≡ (m / d){≢0} + (n / d){≢0}
  +-distrib-/-divMod m n {d'@(suc d)} <-pf =
    +-distrib-/ m n{d'} <-pf

  neg◃-injective : ∀ {m n} → Sign.- ℤ.◃ m ≡ Sign.- ℤ.◃ n → m ≡ n
  neg◃-injective {zero} {zero} eq = refl
  neg◃-injective {suc m} {suc n} eq = cong suc (ℤ.-[1+-injective eq)

  import Data.List as List

  length-─-< : ∀ {ℓ} {A : Set ℓ} (xs : List A) i → length (xs List.─ i) < length xs
  length-─-< (x ∷ xs) Fin.zero = s≤s ≤-refl
  length-─-< (x ∷ xs) (Fin.suc i) = s≤s (length-─-< xs i)

  take-length-++ : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → take (length xs) (xs ++ ys) ≡ xs
  take-length-++ [] ys = refl
  take-length-++ (x ∷ xs) ys = cong (x ∷_) (take-length-++ xs ys)

  drop-length-++ : ∀ {ℓ} {@0 A : Set ℓ} (xs ys : List A) → drop (length xs) (xs ++ ys) ≡ ys
  drop-length-++ [] ys = refl
  drop-length-++ (x ∷ xs) ys = drop-length-++ xs ys

  drop-length : ∀ {ℓ} {@0 A : Set ℓ} (xs : List A) → drop (length xs) xs ≡ []
  drop-length xs = trans₀ (cong (λ x → drop (length xs) x) (sym (++-identityʳ xs))) (drop-length-++ xs [])

  drop-length-≤ : ∀ {ℓ} {A : Set ℓ} (xs₁ ys₁ xs₂ ys₂ : List A) → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂
                  → length xs₁ ≤ length xs₂
                  → xs₂ ≡ xs₁ ++ drop (length xs₁) xs₂
  drop-length-≤ [] ys₁ xs₂ ys₂ xs≡ z≤n = refl
  drop-length-≤ (x ∷ xs₁) ys₁ (x₁ ∷ xs₂) ys₂ xs≡ (s≤s xs₁≤) =
    cong₂ _∷_ (∷-injectiveˡ (sym xs≡)) (drop-length-≤ xs₁ ys₁ xs₂ ys₂ (∷-injectiveʳ xs≡) xs₁≤)

  drop-length-≤-++ : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) (n : ℕ)
                     → n ≤ length xs
                     → drop n xs ++ ys ≡ drop n (xs ++ ys)
  drop-length-≤-++ xs ys zero n≤ = refl
  drop-length-≤-++ (x ∷ xs) ys (suc n) (s≤s n≤) = drop-length-≤-++ xs ys n n≤

  length-++-≡ : ∀ {ℓ} {A : Set ℓ} (ws xs ys zs : List A) → ws ++ xs ≡ ys ++ zs → length ws ≡ length ys → ws ≡ ys × xs ≡ zs
  length-++-≡ [] xs [] zs ++-≡ len≡ = refl , ++-≡
  length-++-≡ (x ∷ ws) xs (x₁ ∷ ys) zs ++-≡ len≡
    with length-++-≡ ws xs ys zs (∷-injectiveʳ ++-≡) (cong pred len≡)
  ...| refl , xs≡zs = cong (_∷ ws) (∷-injectiveˡ ++-≡) , xs≡zs

  ++-≡-⊆ : ∀ {ℓ} {A : Set ℓ} (ws xs ys zs : List A) → ws ++ xs ≡ ys ++ zs → ∃[ n ] ( ws ++ take n xs ≡ ys ⊎  ws ≡ ys ++ take n zs)
  ++-≡-⊆ [] xs [] zs eq = 0 , inj₁ refl
  ++-≡-⊆ [] (x₁ ∷ xs) (x ∷ ys) zs eq =
    1 + length ys
    , inj₁ (begin take (1 + length ys) (x₁ ∷ xs)
                    ≡⟨ cong (take (1 + length ys)) eq ⟩
                  take (1 + length ys) (x ∷ ys ++ zs)
                    ≡⟨ cong (x ∷_) (take-length-++ ys zs) ⟩
                  x ∷ ys ∎)
    where open ≡-Reasoning
  ++-≡-⊆ (x ∷ ws) xs [] zs eq =
    1 + length ws
    , inj₂ (begin (x ∷ ws ≡⟨ sym (cong (x ∷_) (take-length-++ ws xs)) ⟩
                  take (length (x ∷ ws)) (x ∷ ws ++ xs) ≡⟨ cong (take (1 + length ws)) eq ⟩
                  take (length (x ∷ ws)) zs ∎))
    where open ≡-Reasoning
  ++-≡-⊆ (x ∷ ws) xs (x₁ ∷ ys) zs eq
    with ∷-injectiveˡ eq
  ... | refl
    with ++-≡-⊆ ws xs ys zs (∷-injectiveʳ eq)
  ... | n , inj₁ ys⊆ = n , inj₁ (cong (x ∷_) ys⊆)
  ... | n , inj₂ ws⊆ = n , inj₂ (cong (x ∷_) ws⊆)

  ⊆⇒++take
    : ∀ {ℓ} {A : Set ℓ} {xs₁ ys₁ xs₂ ys₂ : List A} → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂
      → length xs₁ ≤ length xs₂
      → Σ[ n ∈ ℕ ] xs₂ ≡ xs₁ ++ take n ys₁
  ⊆⇒++take {xs₁ = xs₁}{ys₁}{xs₂}{ys₂} ++≡ xs₁≤xs₂ =
      (length (drop (length xs₁) xs₂))
    , (xs₂ ≡⟨ xs₂≡ ⟩
      xs₁ ++ drop (length xs₁) xs₂
        ≡⟨ cong (xs₁ ++_) (sym (take-length-++ (drop (length xs₁) xs₂) ys₂)) ⟩
      xs₁ ++ take (length (drop (length xs₁) xs₂)) (drop (length xs₁) xs₂ ++ ys₂)
        ≡⟨ cong (λ x → xs₁ ++ take (length (drop (length xs₁) xs₂)) x) (sym ys₁≡) ⟩
      xs₁ ++ take (length (drop (length xs₁) xs₂)) ys₁ ∎ )
    where
    open ≡-Reasoning

    xs₂≡ : xs₂ ≡ xs₁ ++ drop (length xs₁) xs₂
    xs₂≡ = drop-length-≤ xs₁ ys₁ xs₂ ys₂ ++≡ xs₁≤xs₂

    ys₁≡ : ys₁ ≡ drop (length xs₁) xs₂ ++ ys₂
    ys₁≡ = ++-cancelˡ xs₁
      (xs₁ ++ ys₁ ≡⟨ ++≡ ⟩
      xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) xs₂≡ ⟩
      (xs₁ ++ drop (length xs₁) xs₂) ++ ys₂ ≡⟨ ++-assoc xs₁ _ _ ⟩
      xs₁ ++ drop (length xs₁) xs₂ ++ ys₂ ∎)

  length-++-≤₁ : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → length xs ≤ length (xs ++ ys)
  length-++-≤₁ [] ys = z≤n
  length-++-≤₁ (x ∷ xs) ys = s≤s (length-++-≤₁ xs ys)

  length-++-< : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → xs ≢ [] → length ys < length (xs ++ ys)
  length-++-< [] ys xs≢[] = contradiction refl xs≢[]
  length-++-< (x ∷ xs) ys xs≢[] = begin
    1 +             length ys ≤⟨ s≤s (m≤n+m (length ys) (length xs)) ⟩
    1 + length xs + length ys ≡⟨ cong suc (sym (length-++ xs)) ⟩
    1 + length (xs ++ ys)     ≡⟨ refl ⟩
    length (x ∷ xs ++ ys)     ∎
    where
    open ≤-Reasoning

  ++-cancel≡ˡ : ∀ {ℓ} {@0 A : Set ℓ} (@0 ws xs : List A) {@0 ys zs : List A} → ws ≡ xs
                → ws ++ ys ≡ xs ++ zs → ys ≡ zs
  ++-cancel≡ˡ .xs xs refl eq = ‼ ++-cancelˡ xs eq

  ≡⇒≤ : ∀ {m n} → m ≡ n → m ≤ n
  ≡⇒≤ refl = ≤-refl

  all-++-≡ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (P : A → Set ℓ₂)
             → ∀ {ws x xs ys z zs}
             → All P ws → ¬ P x → All P ys → ¬ P z
             → ws ++ [ x ] ++ xs ≡ ys ++ [ z ] ++ zs
             → ws ≡ ys
  all-++-≡ P [] ¬x [] ¬z eq = refl
  all-++-≡ P [] ¬x (px ∷ allys) ¬z eq =
    contradiction (subst P (sym $ ∷-injectiveˡ eq) px) ¬x
  all-++-≡ P (px ∷ allws) ¬x [] ¬z eq =
    contradiction (subst P (∷-injectiveˡ eq) px) ¬z
  all-++-≡ P (px ∷ allws) ¬x (px₁ ∷ allys) ¬z eq
    with ∷-injectiveˡ eq
  ... | refl = cong (_ ∷_) (all-++-≡ _ allws ¬x allys ¬z (∷-injectiveʳ eq))

  ∷ʳ⇒≢[] : ∀ {ℓ} {A : Set ℓ} {xs : List A} {y} → xs ∷ʳ y ≢ []
  ∷ʳ⇒≢[] {xs = []} ()
  ∷ʳ⇒≢[] {xs = x ∷ xs} ()

  lookup-index : ∀ {ℓ} {@0 A : Set ℓ} {x : A} {xs : List A}
                 → (x∈ : x ∈ xs)
                 → lookup xs (Any.index x∈) ≡ x
  lookup-index (here refl) = refl
  lookup-index (there x∈) = lookup-index x∈

  toListLength : ∀ {ℓ} {@0 A : Set ℓ} {n} → (xs : Vec A n) → length (Vec.toList xs) ≡ n
  toListLength [] = refl
  toListLength (x ∷ xs) = cong suc (toListLength xs)

  toList-injective : ∀ {ℓ} {@0 A : Set ℓ} {n} → (xs₁ xs₂ : Vec A n)
                     → Vec.toList xs₁ ≡ Vec.toList xs₂
                     → xs₁ ≡ xs₂
  toList-injective [] [] xs≡ = refl
  toList-injective (x ∷ xs₁) (x₁ ∷ xs₂) xs≡ =
    ‼ cong₂ Vec._∷_ (∷-injectiveˡ xs≡) (toList-injective xs₁ xs₂ (∷-injectiveʳ xs≡))

  fromList∘toList : ∀ {ℓ} {@0 A : Set ℓ} {n} (xs : Vec A n) → subst (Vec A) (toListLength xs) (Vec.fromList (Vec.toList xs)) ≡ xs
  fromList∘toList [] = refl
  fromList∘toList{A = A} (x ∷ xs) = ‼ (begin
    subst (Vec A) (cong suc (toListLength xs)) (Vec.fromList (Vec.toList (x ∷ xs)))
      ≡⟨⟩
    subst (Vec A) (cong suc (toListLength xs)) (x ∷ Vec.fromList (Vec.toList xs))
      ≡⟨ ≡-elim
           (λ {n} eq →
              subst (Vec A) (cong suc eq) (x ∷ Vec.fromList (Vec.toList xs))
            ≡ x ∷ subst (Vec A) eq (Vec.fromList (Vec.toList xs)))
           refl (toListLength xs) ⟩
    x ∷ subst (Vec A) (toListLength xs) (Vec.fromList (Vec.toList xs)) ≡⟨ cong (x ∷_) (fromList∘toList xs) ⟩
    x ∷ xs ∎)
    where
    open ≡-Reasoning

  replicate-+ : ∀ {ℓ} {@0 A : Set ℓ} (m n : ℕ) → (x : A) → replicate (m + n) x ≡ replicate m x ++ replicate n x
  replicate-+ zero n x = refl
  replicate-+ (suc m) n x = ‼ cong (x ∷_) (replicate-+ m n x)

  reverse-take : ∀ {ℓ} {@0 A : Set ℓ} (n : ℕ) (xs : List A)
                 → reverse (take n xs) ≡ drop (length xs - n) (reverse xs)
  reverse-take zero xs = ‼ (begin
    [] ≡⟨ sym (drop-length (reverse xs)) ⟩
    drop (length (reverse xs)) (reverse xs)
      ≡⟨ cong (λ x → drop x (reverse xs)) (length-reverse xs) ⟩
    drop (length xs) (reverse xs) ∎)
    where
    open ≡-Reasoning
  reverse-take (suc n) [] = refl
  reverse-take (suc n) (x ∷ xs) = ‼ (begin
    reverse (x ∷ take n xs) ≡⟨ unfold-reverse x (take n xs) ⟩
    reverse (take n xs) ++ [ x ] ≡⟨ cong (_++ [ x ]) (reverse-take n xs) ⟩
    drop (length xs - n) (reverse xs) ++ [ x ] ≡⟨⟩
    drop (length (x ∷ xs) - (suc n)) (reverse xs) ++ [ x ]
      ≡⟨ drop-length-≤-++ (reverse xs) [ x ] ((length (x ∷ xs) - (suc n)))
           (≤-trans (m∸n≤m (length xs) n) (≡⇒≤ (sym (length-reverse xs)))) ⟩
    drop (length (x ∷ xs) - (suc n)) (reverse xs ++ [ x ])
      ≡⟨ cong (λ y → drop (length xs ∸ n) y) (sym (unfold-reverse x xs)) ⟩
    drop (length (x ∷ xs) - (suc n)) (reverse (x ∷ xs)) ∎)
    where
    open ≡-Reasoning
    open import Data.Nat.Properties

  All-reverse : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂}
                → ∀ xs → All P xs → All P (reverse xs)
  All-reverse [] a = a
  All-reverse{P = P} (x ∷ xs) (p ∷ a) rewrite unfold-reverse x xs =
    All.++⁺ (All P (reverse xs) ∋ All-reverse xs a) (p ∷ [])

  import Relation.Binary.HeterogeneousEquality as ≅
  open ≅ using (_≅_ ; refl)

  -- https://stackoverflow.com/questions/26841142/how-to-prove-unfold-reverse-for-vec
  Vec-unfold-reverse
    : ∀ {ℓ} {A : Set ℓ} {n} → (x : A) (xs : Vec A n)
      → Vec.reverse (x ∷ xs) ≅ Vec.reverse xs Vec.++ Vec.[ x ]
  Vec-unfold-reverse{A = A} x xs =
    begin
      Vec.reverse (x ∷ xs) ≅⟨ refl ⟩
      Vec.foldl (Vec _ ∘ (1 +_)) (flip _∷_) Vec.[ x ] xs
        ≅⟨ Vec.foldl-cong{B = Vec _ ∘ (1 +_)}{f = flip _∷_}{C = Vec _ ∘ (_+ 1)}{g = flip _∷_}
             (λ where
               {n'}{h₁}{y}{z} x₁ →
                 ≅.icong (Vec _) (+-comm 1 n') (h₁ Vec.∷_) x₁)
             refl xs
        ⟩
      (Vec.foldl (Vec _ ∘ (_+ 1)) (flip _∷_) Vec.[ x ] xs ≅⟨ helper Vec.[ x ] xs ⟩
      (Vec.reverse xs Vec.++ Vec.[ x ] ∎))
    where
    open ≅.≅-Reasoning

    import Data.Vec.Properties.WithK as Vec

    helper : ∀ {n m} (xs : Vec A n) (ys : Vec A m)
             → Vec.foldl (Vec A ∘ (_+ n)) (flip _∷_) xs ys ≅ Vec.reverse ys Vec.++ xs
    helper xs [] = refl
    helper{n}{m} xs (_∷_{n'} y ys) = begin
      Vec.foldl (Vec A ∘ (_+ n)) (flip _∷_) xs (y ∷ ys) ≅⟨ refl ⟩
      Vec.foldl (Vec A ∘ suc ∘ (_+ n)) (flip _∷_) (y ∷ xs) ys
        ≅⟨ Vec.foldl-cong
             (λ {n'}{h₁}{ws₁}{ws₂} ws≅ →
               ≅.icong{I = ℕ} (Vec _){B = λ {k} _ → Vec _ (suc k)} (sym (+-suc n' _)) (h₁ ∷_) ws≅)
             refl ys
        ⟩
      Vec.foldl (Vec A ∘ (_+ suc n)) (flip _∷_) (y ∷ xs) ys ≅⟨ helper (y ∷ xs) ys ⟩
      Vec.reverse ys Vec.++ (y ∷ xs) ≅⟨ refl ⟩
      Vec.reverse ys Vec.++ (Vec.[ y ] Vec.++ xs)
        ≅⟨ ≅.sym (Vec.++-assoc (Vec.reverse ys) Vec.[ y ] xs) ⟩
      (Vec.reverse ys Vec.++ Vec.[ y ]) Vec.++ xs
        ≅⟨ ≅.icong (Vec _) {B = _} (+-comm n' 1) (Vec._++ xs)
             (≅.sym (Vec-unfold-reverse y ys)) ⟩
      Vec.reverse (y ∷ ys) Vec.++ xs ∎

  Vec-++-identityʳ : ∀ {ℓ} {A : Set ℓ} {n} → (xs : Vec A n) → xs Vec.++ [] ≅ xs
  Vec-++-identityʳ {n} [] = refl
  Vec-++-identityʳ{A = A} {suc n} (x ∷ xs) = ≅.icong (Vec A) (+-identityʳ n) (x Vec.∷_) (Vec-++-identityʳ xs)
    where
    import Relation.Binary.HeterogeneousEquality as ≅
    import Relation.Binary.HeterogeneousEquality.Core as ≅-Core
    import Data.Vec.Properties as Vec

    open ≅ using (_≅_ ; refl)
    open ≅.≅-Reasoning

  Vec-++-assoc
    : ∀ {ℓ} {A : Set ℓ} {m} {n} {o}
      → (xs : Vec A m) (ys : Vec A n) (zs : Vec A o)
      → (xs Vec.++ ys) Vec.++ zs ≅ xs Vec.++ ys Vec.++ zs
  Vec-++-assoc [] ys zs = refl
  Vec-++-assoc{m = suc m}{n}{o} (x ∷ xs) ys zs =
    ≅.icong (Vec _) {x = (xs Vec.++ ys) Vec.++ zs}{y = xs Vec.++ ys Vec.++ zs}
      (+-assoc m n o)
      (x Vec.∷_)
      (Vec-++-assoc xs ys zs)
    where
    import Relation.Binary.HeterogeneousEquality as ≅
    import Relation.Binary.HeterogeneousEquality.Core as ≅-Core
    import Data.Vec.Properties as Vec

    open ≅ using (_≅_ ; refl)
    open ≅.≅-Reasoning

  Vec-reverse-++
    : ∀ {ℓ} {A : Set ℓ} {m n} → (xs : Vec A m) (ys : Vec A n)
      → Vec.reverse (xs Vec.++ ys) ≅ Vec.reverse ys Vec.++ Vec.reverse xs
  Vec-reverse-++ {m = .zero} {n} [] ys = begin
    Vec.reverse ys ≅⟨ ≅.sym (Vec-++-identityʳ (Vec.reverse ys)) ⟩
    Vec.reverse ys Vec.++ [] ∎
    where
    import Relation.Binary.HeterogeneousEquality as ≅
    import Relation.Binary.HeterogeneousEquality.Core as ≅-Core
    import Data.Vec.Properties as Vec

    open ≅ using (_≅_ ; refl)
    open ≅.≅-Reasoning

  Vec-reverse-++{A = A} {suc m} {n} (x ∷ xs) ys = begin
    Vec.reverse (x ∷ xs Vec.++ ys) ≅⟨ Vec-unfold-reverse x (xs Vec.++ ys) ⟩
    Vec.reverse (xs Vec.++ ys) Vec.++ Vec.[ x ]
      ≅⟨ ≅.icong (Vec A) {i = m + n} {j = n + m}
           {x = Vec.reverse (xs Vec.++ ys)}
           {y = Vec.reverse ys Vec.++ Vec.reverse xs}
           (+-comm m n)
           (Vec._++ Vec.[ x ])
           (Vec-reverse-++ xs ys) ⟩
    (Vec.reverse ys Vec.++ Vec.reverse xs) Vec.++ Vec.[ x ]
      ≅⟨ Vec-++-assoc (Vec.reverse ys) (Vec.reverse xs) Vec.[ x ] ⟩
    (Vec.reverse ys Vec.++ Vec.reverse xs Vec.++ Vec.[ x ]
      ≅⟨ ≅.icong (Vec A)
           {x = Vec.reverse xs Vec.++ Vec.[ x ]}{y = Vec.reverse (x ∷ xs)}
           (+-comm m 1)
           (Vec.reverse ys Vec.++_)
           (≅.sym (Vec-unfold-reverse x xs)) ⟩
    Vec.reverse ys Vec.++ Vec.reverse (x ∷ xs) ∎)
    where
    import Relation.Binary.HeterogeneousEquality as ≅
    import Relation.Binary.HeterogeneousEquality.Core as ≅-Core
    import Data.Vec.Properties as Vec

    open ≅ using (_≅_ ; refl)
    open ≅.≅-Reasoning

  Vec-reverse-injective : ∀ {ℓ} {A : Set ℓ} {n} (xs ys : Vec A n)
                          → Vec.reverse xs ≡ Vec.reverse ys
                        → xs ≡ ys
  Vec-reverse-injective {ℓ} {A} {.zero} [] [] xs≡ys = refl
  Vec-reverse-injective {ℓ} {A} {.(suc _)} (_∷_{n} x xs) (y ∷ ys) xs≡ys =
    ≅-Core.≅-to-≡ (begin
      (x ∷ xs
        ≅⟨
          ≅.icong₂{I = ℕ}
            (λ _ → A){i = 0} refl
            (Vec._∷_{n = n})
            (≅-Core.≡-to-≅ (Vec.∷-injectiveˡ (Vec.++-injectiveʳ (Vec.reverse xs) (Vec.reverse ys) (≅-Core.≅-to-≡ xs≅ys))))
            (≅-Core.≡-to-≅ ih) ⟩
      y ∷ ys ∎))
    where
    import Relation.Binary.HeterogeneousEquality as ≅
    import Relation.Binary.HeterogeneousEquality.Core as ≅-Core
    import Data.Vec.Properties as Vec

    open ≅ using (_≅_ ; refl)
    open ≅.≅-Reasoning

    xs≅ys : Vec.reverse xs Vec.++ Vec.[ x ] ≅ Vec.reverse ys Vec.++ Vec.[ y ]
    xs≅ys = begin
      (Vec.reverse xs Vec.++ Vec.[ x ] ≅⟨ ≅.sym (Vec-unfold-reverse x xs) ⟩
      Vec.reverse (x ∷ xs) ≅⟨ ≅-Core.≡-to-≅ xs≡ys ⟩
      Vec.reverse (y ∷ ys) ≅⟨ Vec-unfold-reverse y ys ⟩
      Vec.reverse ys Vec.++ Vec.[ y ] ∎)

    ih =
      Vec-reverse-injective xs ys
        (Vec.++-injectiveˡ (Vec.reverse xs) (Vec.reverse ys)
          (≅-Core.≅-to-≡ xs≅ys))

  Vec-reverse-inverse : ∀ {ℓ} {A : Set ℓ} {n} → (xs : Vec A n) → Vec.reverse (Vec.reverse xs) ≡ xs
  Vec-reverse-inverse {n} [] = refl
  Vec-reverse-inverse{A = A} {suc n} (x ∷ xs) = ≅-Core.≅-to-≡ (begin
    Vec.reverse (Vec.reverse (x ∷ xs))
      ≅⟨ ≅.icong (Vec A){x = Vec.reverse (x ∷ xs)}{y = Vec.reverse xs Vec.++ Vec.[ x ]}
           (+-comm 1 n)
           Vec.reverse
           (Vec-unfold-reverse x xs) ⟩
    Vec.reverse (Vec.reverse xs Vec.++ Vec.[ x ]) ≅⟨ Vec-reverse-++ (Vec.reverse xs) Vec.[ x ] ⟩
    (x ∷ Vec.reverse (Vec.reverse xs) ≅⟨ ≅.icong (Vec A) refl (x Vec.∷_) (≅-Core.≡-to-≅ (Vec-reverse-inverse xs)) ⟩
    (x ∷ xs ∎)))
    where
    import Relation.Binary.HeterogeneousEquality as ≅
    import Relation.Binary.HeterogeneousEquality.Core as ≅-Core
    import Data.Vec.Properties as Vec

    open ≅ using (_≅_ ; refl)
    open ≅.≅-Reasoning

  Fin-toℕ-subst : ∀ {m n} {eq : m ≡ n} → (i : Fin m) → toℕ (subst Fin eq i) ≡ toℕ i
  Fin-toℕ-subst{eq = refl} i = refl

  Fin-toℕ-2* : ∀ {m} → (i : Fin m) → toℕ (Fin.2* i) ≡ 2 * toℕ i
  Fin-toℕ-2* {.(suc _)} Fin.zero = Fin-toℕ-subst Fin.zero
  Fin-toℕ-2* {.(suc _)} (Fin.suc{suc _} i) = begin
    toℕ (subst Fin _ (Fin.suc (Fin.suc (Fin.2* i)))) ≡⟨ Fin-toℕ-subst (Fin.suc (Fin.suc (Fin.2* i))) ⟩
    suc (suc (toℕ (Fin.2* i))) ≡⟨ cong (2 +_) (Fin-toℕ-2* i) ⟩
    suc (suc (toℕ i + (toℕ i + 0))) ≡⟨ cong suc (sym (+-suc (toℕ i) (toℕ i + 0))) ⟩
    suc (toℕ i + suc (toℕ i + 0)) ∎
    where
    open ≡-Reasoning
