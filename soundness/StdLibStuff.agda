module StdLibStuff where


{-
-- Data.Empty

data ⊥ : Set where

-- Relation.Nullary.Core

infix 3 ¬_

¬_ : Set → Set
¬ P = P → ⊥

data Dec (P : Set) : Set where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P
-}

-- Relation.Binary.Core

infix 4 _≡_  -- _≢_

data _≡_ {A : Set} (x : A) : A → Set where
 refl : x ≡ x

{-
_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ x ≡ y

Decidable : {A : Set} → Set
Decidable {A} = (x y : A) → Dec (x ≡ y)
-}

-- equality properties

sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

subst : {A : Set} → {x y : A} → (p : A → Set) → x ≡ y → p x → p y
subst p refl h = h

cong : {A B : Set} → {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

trans : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl h = h

{-
-- Data.List

infixr 5 _∷_

data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

data List₁ (A : Set₁) : Set₁ where
  []  : List₁ A
  _∷_ : (x : A) (xs : List₁ A) → List₁ A
-}

-- Data.Bool

infixr 5 _∨_

data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true  = false
not false = true

_∨_ : Bool → Bool → Bool
true  ∨ b = true
false ∨ b = b

{-
-- Data.Product

infixr 4 _,_ _,′_

infixr 2 _×_

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

record Σ₁ (A : Set₁) (B : A → Set) : Set₁ where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁


-- nondep product

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_ public

_,′_ : {A B : Set} → A → B → A × B
_,′_ = _,_

∃ : ∀ {A : Set} → (A → Set) → Set
∃ = Σ _

∃₁ : ∀ {A : Set₁} → (A → Set) → Set₁
∃₁ = Σ₁ _
-}

-- Data.Nat

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ    #-}

-- Data.Fin

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)


{-
-- Data.Vec

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

data Vec₁ (A : Set₁) : ℕ → Set₁ where
  []  : Vec₁ A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec₁ A n) → Vec₁ A (suc n)

lookup : ∀ {n} {A : Set} → Fin n → Vec A n → A
lookup zero    (x ∷ xs) = x
lookup (suc i) (x ∷ xs) = lookup i xs

lookup₁ : ∀ {n} {A : Set₁} → Fin n → Vec₁ A n → A
lookup₁ zero    (x ∷ xs) = x
lookup₁ (suc i) (x ∷ xs) = lookup₁ i xs

-- Data.Sum

infixr 1 _⊎_

data _⊎_ (A : Set) (B : Set) : Set where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

[_,_]′ : ∀ {A : Set} {B : Set} {C : Set} →
         (A → C) → (B → C) → (A ⊎ B → C)
[_,_]′ h₁ h₂ (inj₁ x) = h₁ x
[_,_]′ h₁ h₂ (inj₂ y) = h₂ y

--

_↔_ : Set → Set → Set
X ↔ Y = (X → Y) × (Y → X)

-- Misc

record ⊤ : Set where

-}
