module FSC where

-- focused sequent calculus

{-
open import Relation.Binary.PropositionalEquality
open import Data.Nat hiding (_>_)
-}

open import StdLibStuff

open import Syntax


data FSC-Ctx (n : ℕ) : Ctx n → Set where
 ε : FSC-Ctx n ε
 _∷_ : {Γ : Ctx n} → (t : Type n) → FSC-Ctx n Γ → FSC-Ctx n (t ∷ Γ)
 _∷h_ : {Γ : Ctx n} → Form Γ $o → FSC-Ctx n Γ → FSC-Ctx n Γ

data HVar {n : ℕ} : {Γ-t : Ctx n} → FSC-Ctx n Γ-t → Set where
 zero : {Γ-t : Ctx n} {h : Form Γ-t $o} {Γ : FSC-Ctx n Γ-t} → HVar (h ∷h Γ)
 succ : {Γ-t : Ctx n} {h : Form Γ-t $o} {Γ : FSC-Ctx n Γ-t} → HVar Γ → HVar (h ∷h Γ)
 skip : {Γ-t : Ctx n} {t : Type n} {Γ : FSC-Ctx n Γ-t} → HVar Γ → HVar (t ∷ Γ)

lookup-hyp : {n : ℕ} {Γ-t : Ctx n} (Γ : FSC-Ctx n Γ-t) → HVar Γ → Form Γ-t $o
lookup-hyp .(h ∷h Γ) (zero {._} {h} {Γ}) = h
lookup-hyp .(h ∷h Γ) (succ {._} {h} {Γ} x) = lookup-hyp Γ x
lookup-hyp .(t ∷ Γ) (skip {Γ-t} {t} {Γ} x) = weak (lookup-hyp Γ x)

mutual
 data _⊢_ {n : ℕ} {Γ-t : Ctx n} (Γ : FSC-Ctx n Γ-t) : Form Γ-t $o → Set where
  ||-I-l : {F G : Form Γ-t $o} →
         Γ ⊢ F →
         Γ ⊢ (F || G)
  ||-I-r : {F G : Form Γ-t $o} →
         Γ ⊢ G →
         Γ ⊢ (F || G)
  &-I : {F G : Form Γ-t $o} →
         Γ ⊢ F →   Γ ⊢ G →
         Γ ⊢ (F & G)
  ?-I : {t : Type n} {F : Form (t ∷ Γ-t) $o}
   (G : Form Γ-t t) →
   Γ ⊢ sub G F →
   Γ ⊢ (?[ t ] F)
  ?'-I : {t : Type n} {F : Form Γ-t (t > $o)}
   (G : Form Γ-t t) →
   Γ ⊢ (F · G) →
   Γ ⊢ (?'[ t ] F)
  =>-I : {F G : Form Γ-t $o} →
        (F ∷h Γ) ⊢ G →
        Γ ⊢ (F => G)
  ~-I : {F : Form Γ-t $o} →
        (F ∷h Γ) ⊢ $false →
        Γ ⊢ (~ F)
  !-I : {t : Type n} {F : Form (t ∷ Γ-t) $o} →
   (t ∷ Γ) ⊢ F →
   Γ ⊢ (![ t ] F)
  !'-I : {t : Type n} {F : Form Γ-t (t > $o)} →
   (t ∷ Γ) ⊢ (weak F · ($ this {refl})) →
   Γ ⊢ (!'[ t ] F)
  $true-I :
   Γ ⊢ $true
  ==-I : {t : Type n} {F G : Form Γ-t t} →
   Γ ⊢ t ∋ F == G →
   Γ ⊢ (F == G)  -- compute eq

  elim : {F : Form Γ-t $o} →
   (x : HVar Γ) →
   Γ , lookup-hyp Γ x ⊢ F →
   Γ ⊢ F
  ac : {t : Type n} {F : Form Γ-t $o} →
   Γ , (![ t > $o ] ((?[ t ] ($ (next this) {refl} · $ this {refl})) => ($ this {refl} · (ι t ($ (next this) {refl} · $ this {refl}))))) ⊢ F →
   Γ ⊢ F
  ac' : {t : Type n} {F : Form Γ-t $o} →
   Γ , (![ t > $o ] ((?'[ t ] ($ this {refl})) => ($ this {refl} · (ι' t ($ this {refl}))))) ⊢ F →
   Γ ⊢ F

  raa : {F : Form Γ-t $o} →
   Γ ⊢ (~ (~ F)) →
   Γ ⊢ F

  reduce : {t u : Type n} {F : Form Γ-t u → Form Γ-t $o} {G : Form (t ∷ Γ-t) u} {H : Form Γ-t t} →
   Γ ⊢ (F (sub H G)) →
   Γ ⊢ (F ((^[ t ] G) · H))


 data _,_⊢_ {n : ℕ} {Γ-t : Ctx n} (Γ : FSC-Ctx n Γ-t) : Form Γ-t $o → Form Γ-t $o → Set where
  use : {F G : Form Γ-t $o} →
   Γ ⊢ $o ∋ G ↔ F →
   Γ , F ⊢ G
  $false-E : {H : Form Γ-t $o} →
   Γ , $false ⊢ H
  ~-E : {F H : Form Γ-t $o} →
   Γ ⊢ F →
   Γ , ~ F ⊢ H
  ||-E : {F G H : Form Γ-t $o} →
   Γ ⊢ (F => H) →
   Γ ⊢ (G => H) →
   Γ , F || G ⊢ H

  &-E-l : {F G H : Form Γ-t $o} →
   Γ , F ⊢ H →
   Γ , F & G ⊢ H
  &-E-r : {F G H : Form Γ-t $o} →
   Γ , G ⊢ H →
   Γ , F & G ⊢ H
  ?-E : {t : Type n} {F : Form (t ∷ Γ-t) $o} {H : Form Γ-t $o} →
   Γ , sub (ι t F) F ⊢ H →
   Γ , ?[ t ] F ⊢ H
  ?'-E : {t : Type n} {F : Form Γ-t (t > $o)} {H : Form Γ-t $o} →
   Γ , (F · ι' t F) ⊢ H →
   Γ , ?'[ t ] F ⊢ H
  =>-E : {F G H : Form Γ-t $o} →
   Γ ⊢ F →
   Γ , G ⊢ H →
   Γ , F => G ⊢ H
  !-E : {t : Type n} {F : Form (t ∷ Γ-t) $o} {H : Form Γ-t $o}
   (G : Form Γ-t t) →
   Γ , sub G F ⊢ H →
   Γ , ![ t ] F ⊢ H
  !'-E : {t : Type n} {F : Form Γ-t (t > $o)} {H : Form Γ-t $o}
   (G : Form Γ-t t) →
   Γ , (F · G) ⊢ H →
   Γ , !'[ t ] F ⊢ H
  r-bool-ext : {F G H : Form Γ-t $o} →
   Γ , ((F => G) & (G => F)) ⊢ H →
   Γ , F == G ⊢ H  -- compute eq
  r-fun-ext : {t u : Type n} {F G : Form Γ-t (t > u)} {H : Form Γ-t $o}
   (I : Form Γ-t t) →
   Γ , (F · I) == (G · I) ⊢ H →
   Γ , F == G ⊢ H  -- compute eq
   

  reduce : {t u : Type n} {F : Form Γ-t u → Form Γ-t $o} {G : Form (t ∷ Γ-t) u} {H : Form Γ-t t} {I : Form Γ-t $o} →
   Γ , (F (sub H G)) ⊢ I →
   Γ , (F ((^[ t ] G) · H)) ⊢ I


 data _⊢_∋_==_ {n : ℕ} {Γ-t : Ctx n} (Γ : FSC-Ctx n Γ-t) : (t : Type n) (F G : Form Γ-t t) → Set where
  simp : {t : Type n} {F G : Form Γ-t t} →
   Γ ⊢ t ∋ F ↔ G →
   Γ ⊢ t ∋ F == G
  step : {t : Type n} {F G : Form Γ-t t} (F' G' : Form Γ-t t) →
   (x : HVar Γ) →
   Γ , lookup-hyp Γ x ⊢ F' == G' →
   Γ ⊢ t ∋ F ↔ F' →
   Γ ⊢ t ∋ G' == G →
   Γ ⊢ t ∋ F == G
  bool-ext :  {F G : Form Γ-t $o} →
   Γ ⊢ ((F => G) & (G => F)) →
   Γ ⊢ $o ∋ F == G
  fun-ext : {t u : Type n} {F G : Form Γ-t (t > u)} →
   (t ∷ Γ) ⊢ u ∋ ((weak F) · $ this {refl}) == ((weak G) · $ this {refl}) →
   Γ ⊢ (t > u) ∋ F == G


 data _⊢_∋_↔_ {n : ℕ} {Γ-t : Ctx n} (Γ : FSC-Ctx n Γ-t) : (t : Type n) → Form Γ-t t → Form Γ-t t → Set where
  head-var : (t : Type n) (x : Var Γ-t) (p : lookup-Var Γ-t x ≡ t) →
   Γ ⊢ t ∋ $ x {p} ↔ $ x {p}
  head-const : (t : Type n) (c : Form Γ-t t) →
   Γ ⊢ t ∋ c ↔ c
  head-app : (t₁ t₂ : Type n) (F₁ F₂ : Form Γ-t (t₁ > t₂)) (G₁ G₂ : Form Γ-t t₁) →
   Γ ⊢ (t₁ > t₂) ∋ F₁ == F₂ → Γ ⊢ t₁ ∋ G₁ == G₂ →
   Γ ⊢ t₂ ∋ (F₁ · G₁) ↔ (F₂ · G₂)
  head-lam : (t₁ t₂ : Type n) (F₁ F₂ : Form (t₁ ∷ Γ-t) t₂) →
   (t₁ ∷ Γ) ⊢ t₂ ∋ F₁ == F₂ →
   Γ ⊢ (t₁ > t₂) ∋ (lam t₁ F₁) ↔ (lam t₁ F₂)
  head-lam-eta-left : (t₁ t₂ : Type n) (F₁ : Form Γ-t (t₁ > t₂)) (F₂ : Form (t₁ ∷ Γ-t) t₂) →
   (t₁ ∷ Γ) ⊢ t₂ ∋ (weak F₁ · $ this {refl}) == F₂ →
   Γ ⊢ (t₁ > t₂) ∋ F₁ ↔ lam t₁ F₂
  head-lam-eta-right : (t₁ t₂ : Type n) (F₁ : Form Γ-t (t₁ > t₂)) (F₂ : Form (t₁ ∷ Γ-t) t₂) →
   (t₁ ∷ Γ) ⊢ t₂ ∋ F₂ == (weak F₁ · $ this {refl}) →
   Γ ⊢ (t₁ > t₂) ∋ lam t₁ F₂ ↔ F₁

  reduce-l : {t u v : Type n} {F₁ : Form Γ-t v → Form Γ-t t} {G : Form (u ∷ Γ-t) v} {H : Form Γ-t u} {F₂ : Form Γ-t t} →
   Γ ⊢ t ∋ (F₁ (sub H G)) ↔ F₂ →
   Γ ⊢ t ∋ (F₁ ((^[ u ] G) · H)) ↔ F₂
  reduce-r : {t u v : Type n} {F₂ : Form Γ-t v → Form Γ-t t} {G : Form (u ∷ Γ-t) v} {H : Form Γ-t u} {F₁ : Form Γ-t t} →
   Γ ⊢ t ∋ F₁ ↔ (F₂ (sub H G)) →
   Γ ⊢ t ∋ F₁ ↔ (F₂ ((^[ u ] G) · H))


 data _,_⊢_==_ {n : ℕ} {Γ-t : Ctx n} {t : Type n} (Γ : FSC-Ctx n Γ-t) : Form Γ-t $o → Form Γ-t t → Form Γ-t t → Set where
  use : {F G : Form Γ-t t} →
   Γ , F == G ⊢ F == G
  use' : {F G : Form Γ-t t} {H : Form Γ-t $o} →
   headNorm 2 (F == G) ≡ headNorm 2 H →
   Γ , H ⊢ F == G
  use-sym : {F G : Form Γ-t t} →
   Γ , F == G ⊢ G == F  -- compute eq

  &-E-l : {F G : Form Γ-t $o} {H₁ H₂ : Form Γ-t t} →
   Γ , F ⊢ H₁ == H₂ →
   Γ , F & G ⊢ H₁ == H₂
  &-E-r : {F G : Form Γ-t $o} {H₁ H₂ : Form Γ-t t} →
   Γ , G ⊢ H₁ == H₂ →
   Γ , F & G ⊢ H₁ == H₂
  ?-E : {u : Type n} {F : Form (u ∷ Γ-t) $o} {H₁ H₂ : Form Γ-t t} →
   Γ , sub (ι u F) F ⊢ H₁ == H₂ →
   Γ , ?[ u ] F ⊢ H₁ == H₂
  ?'-E : {u : Type n} {F : Form Γ-t (u > $o)} {H₁ H₂ : Form Γ-t t} →
   Γ , (F · ι' u F) ⊢ H₁ == H₂ →
   Γ , ?'[ u ] F ⊢ H₁ == H₂
  =>-E : {F G : Form Γ-t $o} {H₁ H₂ : Form Γ-t t} →
   Γ ⊢ F →
   Γ , G ⊢ H₁ == H₂ →
   Γ , F => G ⊢ H₁ == H₂
  !-E : {u : Type n} {F : Form (u ∷ Γ-t) $o} {H₁ H₂ : Form Γ-t t}
   (G : Form Γ-t u) →
   Γ , sub G F ⊢ H₁ == H₂ →
   Γ , ![ u ] F ⊢ H₁ == H₂
  !'-E : {u : Type n} {F : Form Γ-t (u > $o)} {H₁ H₂ : Form Γ-t t}
   (G : Form Γ-t u) →
   Γ , (F · G) ⊢ H₁ == H₂ →
   Γ , !'[ u ] F ⊢ H₁ == H₂
  r-bool-ext : {F G : Form Γ-t $o} {H I : Form Γ-t t} →
   Γ , ((F => G) & (G => F)) ⊢ H == I →
   Γ , F == G ⊢ H == I  -- compute eq
  r-fun-ext : {u v : Type n} {F G : Form Γ-t (u > v)} {H I : Form Γ-t t}
   (J : Form Γ-t u) →
   Γ , (F · J) == (G · J) ⊢ H == I →
   Γ , F == G ⊢ H == I  -- compute eq

  reduce : {u v : Type n} {F : Form Γ-t v → Form Γ-t $o} {G : Form (u ∷ Γ-t) v} {H : Form Γ-t u} {I₁ I₂ : Form Γ-t t} →
   Γ , (F (sub H G)) ⊢ I₁ == I₂ →
   Γ , (F ((^[ u ] G) · H)) ⊢ I₁ == I₂
