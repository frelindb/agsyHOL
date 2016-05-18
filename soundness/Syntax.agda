module Syntax where

{-
open import Data.Nat hiding (_>_)
open import Data.Fin
open import Data.Product
open import Data.Bool
open import Relation.Binary.PropositionalEquality
-}

open import StdLibStuff

erase-subst :
 (X : Set) → (Y : X → Set) →
 (F : {x : X} → Y x) →
 (x₁ x₂ : X) →
 (eq : x₁ ≡ x₂) →
 (P : Y x₂ → Set) →
 P F →
 P (subst Y eq F)
erase-subst X Y F .x₂ x₂ refl P h = h



-- type, ctx

data Type (n : ℕ) : Set where
 $o : Type n
 $i : Fin n → Type n
 _>_ : Type n → Type n → Type n

data Ctx (n : ℕ) : Set where
 ε : Ctx n
 _∷_ : Type n → Ctx n → Ctx n

data Var : {n : ℕ} → Ctx n → Set where
 this : ∀ {n t} → {Γ : Ctx n} → Var (t ∷ Γ)
 next : ∀ {n t} → {Γ : Ctx n} → Var Γ → Var (t ∷ Γ)

lookup-Var : ∀ {n} → (Γ : Ctx n) → Var Γ → Type n
lookup-Var ε ()
lookup-Var (t ∷ _) this = t
lookup-Var (_ ∷ Γ) (next x) = lookup-Var Γ x


_++_ : ∀ {n} → Ctx n → Ctx n → Ctx n
ε ++ Γ = Γ
(t ∷ Γ₁) ++ Γ₂ = t ∷ (Γ₁ ++ Γ₂)

_r++_ : ∀ {n} → Ctx n → Ctx n → Ctx n
ε r++ Γ = Γ
(t ∷ Γ₁) r++ Γ₂ = Γ₁ r++ (t ∷ Γ₂)


-- stt formula

data Form : {n : ℕ} → Ctx n → Type n → Set where
 var : ∀ {n} → {Γ : Ctx n} {t : Type n} → (x : Var Γ) → lookup-Var Γ x ≡ t → Form Γ t
 N : ∀ {n} → {Γ : Ctx n} → Form Γ ($o > $o)
 A : ∀ {n} → {Γ : Ctx n} → Form Γ ($o > ($o > $o))
 Π : ∀ {n α} → {Γ : Ctx n} → Form Γ ((α > $o) > $o)
 i : ∀ {n α} → {Γ : Ctx n} → Form Γ ((α > $o) > α)
 app : ∀ {n α β} → {Γ : Ctx n} → Form Γ (α > β) → Form Γ α → Form Γ β
 lam : ∀ {n β} → {Γ : Ctx n} → (α : _) → Form (α ∷ Γ) β → Form Γ (α > β)


-- abbreviations (TPTP-like notation)

~ : ∀ {n} → {Γ : Ctx n} → Form Γ $o → Form Γ $o
~ F = app N F

_||_ : ∀ {n} → {Γ : Ctx n} → Form Γ $o → Form Γ $o → Form Γ $o
F || G = app (app A F) G

_&_ : ∀ {n} → {Γ : Ctx n} → Form Γ $o → Form Γ $o → Form Γ $o
F & G = ~ ((~ F) || (~ G))

_=>_ : ∀ {n} → {Γ : Ctx n} → Form Γ $o → Form Γ $o → Form Γ $o
F => G = (~ F) || G

![_]_ : ∀ {n} → {Γ : Ctx n} → (α : Type n) → Form (α ∷ Γ) $o → Form Γ $o
![ α ] F = app Π (lam α F)

infix 25 ![_]_

?[_]_ : ∀ {n} → {Γ : Ctx n} → (α : Type n) → Form (α ∷ Γ) $o → Form Γ $o
?[ α ] F = ~ (![ α ] ~ F)

infix 25 ?[_]_

ι : ∀ {n} → {Γ : Ctx n} → (α : Type n) → Form (α ∷ Γ) $o → Form Γ α
ι α F = app i (lam α F)

Q : ∀ {n} → {Γ : Ctx n} → (α : Type n) → Form Γ (α > (α > $o))
Q α = lam α (lam α (![ α > $o ] (app (var this refl) (var (next (next this)) refl) => app (var this refl) (var (next this) refl))))

_==_ : ∀ {n} → {Γ : Ctx n} → {α : Type n} → Form Γ α → Form Γ α → Form Γ $o
F == G = app (app (Q _) F) G

_<=>_ : ∀ {n} → {Γ : Ctx n} → Form Γ $o → Form Γ $o → Form Γ $o
F <=> G = (F => G) & (G => F)

$true : ∀ {n} → {Γ : Ctx n} → Form Γ $o
$true = ![ $o ] (var this refl => var this refl)

$false : ∀ {n} → {Γ : Ctx n} → Form Γ $o
$false = ![ $o ] var this refl

^[_]_ : ∀ {n Γ t₂} → (t₁ : Type n) → Form (t₁ ∷ Γ) t₂ → Form Γ (t₁ > t₂)
^[ tp ] t = lam tp t

infix 25 ^[_]_

_·_ : ∀ {n} → {Γ : Ctx n} → ∀ {t₁ t₂} → Form Γ (t₁ > t₂) → Form Γ t₁ → Form Γ t₂
t₁ · t₂ = app t₁ t₂

$ : ∀ {n Γ} → {t : Type n} (v : Var Γ) → {eq : lookup-Var Γ v ≡ t} → Form Γ t
$ v {p} = var v p


-- occurs in

eq-Var : ∀ {n} {Γ : Ctx n} → Var Γ → Var Γ → Bool 
eq-Var this this = true
eq-Var this (next y) = false
eq-Var (next x) this = false
eq-Var (next x) (next y) = eq-Var x y

occurs : ∀ {n Γ} → {t : Type n} → Var Γ → Form Γ t → Bool
occurs x (var x' p) = eq-Var x x'
occurs x N = false
occurs x A = false
occurs x Π = false
occurs x i = false
occurs x (app f₁ f₂) = occurs x f₁ ∨ occurs x f₂
occurs x (lam α f) = occurs (next x) f


-- weakening and substitution

weak-var : ∀ {n} → {β : Type n} (Γ₁ Γ₂ : Ctx n) → (x : Var (Γ₁ ++ Γ₂)) → Var (Γ₁ ++ (β ∷ Γ₂))
weak-var ε Γ₂ x = next x
weak-var (t ∷ Γ₁) Γ₂ this = this
weak-var (t ∷ Γ₁) Γ₂ (next x) = next (weak-var Γ₁ Γ₂ x)

weak-var-p : ∀ {n} → {β : Type n} (Γ₁ Γ₂ : Ctx n) → (x : Var (Γ₁ ++ Γ₂)) →
             lookup-Var (Γ₁ ++ (β ∷ Γ₂)) (weak-var Γ₁ Γ₂ x) ≡ lookup-Var (Γ₁ ++ Γ₂) x
weak-var-p ε Γ₂ x = refl
weak-var-p (t ∷ Γ₁) Γ₂ this = refl
weak-var-p (t ∷ Γ₁) Γ₂ (next x) = weak-var-p Γ₁ Γ₂ x

weak-i : ∀ {n} → {α β : Type n} (Γ₁ Γ₂ : Ctx n) → Form (Γ₁ ++ Γ₂) α → Form (Γ₁ ++ (β ∷ Γ₂)) α
weak-i Γ₁ Γ₂ (var x p) = var (weak-var Γ₁ Γ₂ x) (trans (weak-var-p Γ₁ Γ₂ x) p)
weak-i Γ₁ Γ₂ N = N
weak-i Γ₁ Γ₂ A = A
weak-i Γ₁ Γ₂ Π = Π
weak-i Γ₁ Γ₂ i = i
weak-i Γ₁ Γ₂ (app f₁ f₂) = app (weak-i Γ₁ Γ₂ f₁) (weak-i Γ₁ Γ₂ f₂)
weak-i Γ₁ Γ₂ (lam α f) = lam α (weak-i (α ∷ Γ₁) Γ₂ f)

weak : ∀ {n} → {Γ : Ctx n} {α β : Type n} → Form Γ α → Form (β ∷ Γ) α
weak {_} {Γ} = weak-i ε Γ

sub-var : ∀ {n} → {α β : Type n} (Γ₁ Γ₂ : Ctx n) → Form Γ₂ α → (x : Var (Γ₁ ++ (α ∷ Γ₂))) → lookup-Var (Γ₁ ++ (α ∷ Γ₂)) x ≡ β → Form (Γ₁ ++ Γ₂) β
sub-var ε Γ₂ g this p = subst (Form Γ₂) p g
sub-var ε Γ₂ g (next x) p = var x p
sub-var (t ∷ Γ₁) Γ₂ g this p = var this p
sub-var (t ∷ Γ₁) Γ₂ g (next x) p = weak (sub-var Γ₁ Γ₂ g x p)

sub-i : ∀ {n} → {α β : Type n} (Γ₁ Γ₂ : Ctx n) → Form Γ₂ α → Form (Γ₁ ++ (α ∷ Γ₂)) β → Form (Γ₁ ++ Γ₂) β
sub-i Γ₁ Γ₂ g (var x p) = sub-var Γ₁ Γ₂ g x p
sub-i Γ₁ Γ₂ g N = N
sub-i Γ₁ Γ₂ g A = A
sub-i Γ₁ Γ₂ g Π = Π
sub-i Γ₁ Γ₂ g i = i
sub-i Γ₁ Γ₂ g (app f₁ f₂) = app (sub-i Γ₁ Γ₂ g f₁) (sub-i Γ₁ Γ₂ g f₂)
sub-i Γ₁ Γ₂ g (lam α f) = lam α (sub-i (α ∷ Γ₁) Γ₂ g f)

sub : ∀ {n} → {Γ : Ctx n} {α β : Type n} → Form Γ α → Form (α ∷ Γ) β → Form Γ β
sub {_} {Γ} = sub-i ε Γ


-- properties about weak and sub

sub-weak-var-p-23-this-2 : ∀ {n} → {u v β : Type n} {Γ : Ctx n} (Γ' : Ctx n) (G : Form (v ∷ Γ) u) →
 (Γ'' : Ctx n)
 (h₁ : β ∷ Γ'' ≡ β ∷ (Γ' ++ (u ∷ (v ∷ Γ))))
 (p'' : lookup-Var ((β ∷ Γ') ++ (u ∷ (v ∷ Γ))) (subst Var h₁ this) ≡ lookup-Var (β ∷ (Γ' ++ (v ∷ Γ))) this) →
 var this refl ≡ sub-var (β ∷ Γ') (v ∷ Γ) G (subst Var h₁ this) p''
sub-weak-var-p-23-this-2 {n} {u} {v} {β} {Γ} Γ' G .(Γ' ++ (u ∷ (v ∷ Γ))) refl refl = refl

sub-weak-var-p-23-this-1 : ∀ {n} → {u v β : Type n} {Γ : Ctx n} (Γ' : Ctx n) (G : Form (v ∷ Γ) u) →
 (h₁ : β ∷ ((Γ' ++ (u ∷ ε)) ++ (v ∷ Γ)) ≡ β ∷ (Γ' ++ (u ∷ (v ∷ Γ))))
 (Γ'' : Ctx n)
 (h₂ : β ∷ Γ'' ≡ β ∷ ((Γ' ++ (u ∷ ε)) ++ Γ))
 (p'' : lookup-Var (β ∷ (Γ' ++ (u ∷ (v ∷ Γ)))) (subst Var h₁ (weak-var (β ∷ (Γ' ++ (u ∷ ε))) Γ (subst Var h₂ this))) ≡ β) →
 var this refl ≡
 sub-var (β ∷ Γ') (v ∷ Γ) G (subst Var h₁ (weak-var (β ∷ (Γ' ++ (u ∷ ε))) Γ (subst Var h₂ this))) p''
sub-weak-var-p-23-this-1 {n} {u} {v} {β} {Γ} Γ' G h₁ .((Γ' ++ (u ∷ ε)) ++ Γ) refl p'' = sub-weak-var-p-23-this-2 Γ' G ((Γ' ++ (u ∷ ε)) ++ (v ∷ Γ)) h₁ p''

mutual
 sub-weak-var-p-23-next-2 : ∀ {n} → {u v β t : Type n} {Γ : Ctx n} (Γ' : Ctx n) (x : Var (Γ' ++ Γ)) (G : Form (v ∷ Γ) u) →
  (p : lookup-Var (Γ' ++ (v ∷ Γ)) (weak-var Γ' Γ x) ≡ β)
  (Γ'' : Ctx n)
  (h₁₁ : t ∷ Γ'' ≡ t ∷ (Γ' ++ (u ∷ (v ∷ Γ))))
  (h₁₂ : (Γ' ++ (u ∷ ε)) ++ (v ∷ Γ) ≡ Γ'')
  (h₂ : Γ' ++ (u ∷ Γ) ≡ (Γ' ++ (u ∷ ε)) ++ Γ)
  (p'' : lookup-Var ((t ∷ Γ') ++ (u ∷ (v ∷ Γ))) (subst Var h₁₁ (next (subst Var h₁₂ (weak-var (Γ' ++ (u ∷ ε)) Γ (subst Var h₂ (weak-var Γ' Γ x)))))) ≡ β) →
  var (next (weak-var Γ' Γ x)) p ≡
  sub-var (t ∷ Γ') (v ∷ Γ) G (subst Var h₁₁ (next (subst Var h₁₂ (weak-var (Γ' ++ (u ∷ ε)) Γ (subst Var h₂ (weak-var Γ' Γ x)))))) p''
 sub-weak-var-p-23-next-2 {n} {u} {v} {β} {t} {Γ} Γ' x G p .(Γ' ++ (u ∷ (v ∷ Γ))) refl h₁₂ h₂ p'' = subst (λ z → var (next {_} {t} (weak-var Γ' Γ x)) p ≡ weak-i ε (Γ' ++ (v ∷ Γ)) z) {-{var (weak-var Γ' Γ x) p} {sub-var Γ' (v ∷ Γ) G (subst Var h₁₂ (weak-var (Γ' ++ (u ∷ ε)) Γ (subst Var h₂ (weak-var Γ' Γ x)))) p''}-} (sub-weak-var-p-23 {n} {u} {v} {β} {Γ} Γ' x G p h₁₂ h₂ p'') refl

 sub-weak-var-p-23-next-1 : ∀ {n} → {u v β t : Type n} {Γ : Ctx n} (Γ' : Ctx n) (x : Var (Γ' ++ Γ)) (G : Form (v ∷ Γ) u) →
  (p : lookup-Var (Γ' ++ (v ∷ Γ)) (weak-var Γ' Γ x) ≡ β)
  (h₁ : t ∷ ((Γ' ++ (u ∷ ε)) ++ (v ∷ Γ)) ≡ t ∷ (Γ' ++ (u ∷ (v ∷ Γ))))
  (Γ'' : Ctx n)
  (h₂₁ : t ∷ Γ'' ≡ t ∷ ((Γ' ++ (u ∷ ε)) ++ Γ))
  (h₂₂ : Γ' ++ (u ∷ Γ) ≡ Γ'')
  (p'' : lookup-Var ((t ∷ Γ') ++ (u ∷ (v ∷ Γ))) (subst Var h₁ (weak-var (t ∷ (Γ' ++ (u ∷ ε))) Γ (subst Var h₂₁ (next (subst Var h₂₂ (weak-var Γ' Γ x)))))) ≡ β) →
  var (next (weak-var Γ' Γ x)) p ≡
  sub-var (t ∷ Γ') (v ∷ Γ) G (subst Var h₁ (weak-var (t ∷ (Γ' ++ (u ∷ ε))) Γ (subst Var h₂₁ (next (subst Var h₂₂ (weak-var Γ' Γ x)))))) p''
 sub-weak-var-p-23-next-1 {n} {u} {v} {β} {t} {Γ} Γ' x G p h₁ .((Γ' ++ (u ∷ ε)) ++ Γ) refl h₂₂ p'' = sub-weak-var-p-23-next-2 Γ' x G p ((Γ' ++ (u ∷ ε)) ++ (v ∷ Γ)) h₁ refl h₂₂ p''

 sub-weak-var-p-23 : ∀ {n} → {u v β : Type n} {Γ : Ctx n} (Γ' : Ctx n) (x : Var (Γ' ++ Γ)) (G : Form (v ∷ Γ) u) →
  (p : lookup-Var (Γ' ++ (v ∷ Γ)) (weak-var Γ' Γ x) ≡ β) →
  (h₁ : (Γ' ++ (u ∷ ε)) ++ (v ∷ Γ) ≡ Γ' ++ (u ∷ (v ∷ Γ))) →
  (h₂ : Γ' ++ (u ∷ Γ) ≡ (Γ' ++ (u ∷ ε)) ++ Γ) →
  (p'' : lookup-Var (Γ' ++ (u ∷ (v ∷ Γ))) (subst Var h₁ (weak-var (Γ' ++ (u ∷ ε)) Γ (subst Var h₂ (weak-var Γ' Γ x)))) ≡ β) →
  var (weak-var Γ' Γ x) p ≡
  sub-var Γ' (v ∷ Γ) G (subst Var h₁ (weak-var (Γ' ++ (u ∷ ε)) Γ (subst Var h₂ (weak-var Γ' Γ x)))) p''
 sub-weak-var-p-23 ε x G refl refl refl refl = refl
 sub-weak-var-p-23 {n} {u} {v} {β} {Γ} (.β ∷ Γ') this G refl h₁ h₂ p'' = sub-weak-var-p-23-this-1 Γ' G h₁ (Γ' ++ (u ∷ Γ)) h₂ p''
 sub-weak-var-p-23 {n} {u} {v} {β} {Γ} (t ∷ Γ') (next x) G p h₁ h₂ p'' = sub-weak-var-p-23-next-1 Γ' x G p h₁ (Γ' ++ (u ∷ Γ)) h₂ refl p''

sub-weak-p-23-var-2 : ∀ {n} → {u v β : Type n} {Γ : Ctx n} (Γ' : Ctx n) (x : Var (Γ' ++ Γ)) (G : Form (v ∷ Γ) u) →
 (p : lookup-Var (Γ' ++ Γ) x ≡ β) →
 (Γ'' : Ctx n) →
 (h₁₁ : Γ'' ≡ Γ' ++ (u ∷ (v ∷ Γ))) →
 (h₁₂ : (Γ' ++ (u ∷ ε)) ++ (v ∷ Γ) ≡ Γ'') →
 (h₂ : Γ' ++ (u ∷ Γ) ≡ (Γ' ++ (u ∷ ε)) ++ Γ) →
 (p'' : lookup-Var Γ'' (subst Var h₁₂ (weak-var (Γ' ++ (u ∷ ε)) Γ (subst Var h₂ (weak-var Γ' Γ x)))) ≡ β) →
 var (weak-var Γ' Γ x) (trans (weak-var-p Γ' Γ x) p) ≡
 sub-i Γ' (v ∷ Γ) G (subst (λ z → Form z β) h₁₁ (var (subst Var h₁₂ (weak-var (Γ' ++ (u ∷ ε)) Γ (subst Var h₂ (weak-var Γ' Γ x)))) p''))
sub-weak-p-23-var-2 {n} {u} {v} {β} {Γ} Γ' x G p .(Γ' ++ (u ∷ (v ∷ Γ))) refl h₁₂ h₂ p'' = sub-weak-var-p-23 Γ' x G (trans (weak-var-p Γ' Γ x) p) h₁₂ h₂ p''

sub-weak-p-23-var-1 : ∀ {n} → {u v β : Type n} {Γ : Ctx n} (Γ' : Ctx n) (x : Var (Γ' ++ Γ)) (G : Form (v ∷ Γ) u) →
 (p : lookup-Var (Γ' ++ Γ) x ≡ β) →
 (h₁ : (Γ' ++ (u ∷ ε)) ++ (v ∷ Γ) ≡ Γ' ++ (u ∷ (v ∷ Γ))) →
 (Γ'' : Ctx n) →
 (h₂₁ : Γ'' ≡ (Γ' ++ (u ∷ ε)) ++ Γ) →
 (h₂₂ : Γ' ++ (u ∷ Γ) ≡ Γ'') →
 (p' : lookup-Var Γ'' (subst Var h₂₂ (weak-var Γ' Γ x)) ≡ β) →
 var (weak-var Γ' Γ x) (trans (weak-var-p Γ' Γ x) p) ≡
 sub-i Γ' (v ∷ Γ) G (subst (λ z → Form z β) h₁ (weak-i (Γ' ++ (u ∷ ε)) Γ (subst (λ z → Form z β) h₂₁ (var (subst Var h₂₂ (weak-var Γ' Γ x)) p'))))
sub-weak-p-23-var-1 {n} {u} {v} {β} {Γ} Γ' x G p h₁ .((Γ' ++ (u ∷ ε)) ++ Γ) refl h₂₂ p' = sub-weak-p-23-var-2 Γ' x G p ((Γ' ++ (u ∷ ε)) ++ (v ∷ Γ)) h₁ refl h₂₂ (trans (weak-var-p (Γ' ++ (u ∷ ε)) Γ (subst Var h₂₂ (weak-var Γ' Γ x))) p')

mutual
 sub-weak-p-23-app-2 : ∀ {n} → {t u v w : Type n} {Γ : Ctx n} (Γ' : Ctx n) (f₁ : Form (Γ' ++ Γ) (w > t)) (f₂ : Form (Γ' ++ Γ) w) (G : Form (v ∷ Γ) u) →
  (Γ'' : Ctx n) →
  (h₁₁ : Γ'' ≡ Γ' ++ (u ∷ (v ∷ Γ))) →
  (h₁₂ : (Γ' ++ (u ∷ ε)) ++ (v ∷ Γ) ≡ Γ'') →
  (h₂ : Γ' ++ (u ∷ Γ) ≡ (Γ' ++ (u ∷ ε)) ++ Γ) →
  app (weak-i Γ' Γ f₁) (weak-i Γ' Γ f₂) ≡
  sub-i Γ' (v ∷ Γ) G (subst (λ z → Form z t) h₁₁ (app (subst (λ z → Form z (w > t)) h₁₂ (weak-i (Γ' ++ (u ∷ ε)) Γ (subst (λ z → Form z (w > t)) h₂ (weak-i Γ' Γ f₁)))) (subst (λ z → Form z w) h₁₂ (weak-i (Γ' ++ (u ∷ ε)) Γ (subst (λ z → Form z w) h₂ (weak-i Γ' Γ f₂))))))
 sub-weak-p-23-app-2 {n} {t} {u} {v} {w} {Γ} Γ' f₁ f₂ G .(Γ' ++ (u ∷ (v ∷ Γ))) refl h₁₂ h₂ =
  trans (cong (λ z → app z (weak-i Γ' Γ f₂)) (
    sub-weak-p-23-i Γ' f₁ G h₁₂ h₂
   ))
   (cong (λ z → app (sub-i Γ' (v ∷ Γ) G (subst (λ z → Form z (w > t)) h₁₂ (weak-i (Γ' ++ (u ∷ ε)) Γ (subst (λ z → Form z (w > t)) h₂ (weak-i Γ' Γ f₁))))) z) (
    sub-weak-p-23-i Γ' f₂ G h₁₂ h₂
   ))

 sub-weak-p-23-app-1 : ∀ {n} → {t u v w : Type n} {Γ : Ctx n} (Γ' : Ctx n) (f₁ : Form (Γ' ++ Γ) (w > t)) (f₂ : Form (Γ' ++ Γ) w) (G : Form (v ∷ Γ) u) →
  (h₁ : (Γ' ++ (u ∷ ε)) ++ (v ∷ Γ) ≡ Γ' ++ (u ∷ (v ∷ Γ))) →
  (Γ'' : Ctx n) →
  (h₂₁ : Γ'' ≡ (Γ' ++ (u ∷ ε)) ++ Γ) →
  (h₂₂ : Γ' ++ (u ∷ Γ) ≡ Γ'') →
  app (weak-i Γ' Γ f₁) (weak-i Γ' Γ f₂) ≡
  sub-i Γ' (v ∷ Γ) G (subst (λ z → Form z t) h₁ (weak-i (Γ' ++ (u ∷ ε)) Γ (subst (λ z → Form z t) h₂₁ (app (subst (λ z → Form z (w > t)) h₂₂ (weak-i Γ' Γ f₁)) (subst (λ z → Form z w) h₂₂ (weak-i Γ' Γ f₂))))))
 sub-weak-p-23-app-1 {n} {t} {u} {v} {w} {Γ} Γ' f₁ f₂ G h₁ .((Γ' ++ (u ∷ ε)) ++ Γ) refl h₂₂ = sub-weak-p-23-app-2 Γ' f₁ f₂ G ((Γ' ++ (u ∷ ε)) ++ (v ∷ Γ)) h₁ refl h₂₂

 sub-weak-p-23-lam-2 : ∀ {n} → {u v α β : Type n} {Γ : Ctx n} (Γ' : Ctx n) (f : Form ((α ∷ Γ') ++ Γ) β) (G : Form (v ∷ Γ) u) →
  (Γ'' : Ctx n) →
  (h₁₁ : Γ'' ≡ Γ' ++ (u ∷ (v ∷ Γ))) →
  (h₁₂ : (Γ' ++ (u ∷ ε)) ++ (v ∷ Γ) ≡ Γ'') →
  (h₂ : α ∷ (Γ' ++ (u ∷ Γ)) ≡ α ∷ ((Γ' ++ (u ∷ ε)) ++ Γ)) →
  lam α (weak-i (α ∷ Γ') Γ f) ≡
  sub-i Γ' (v ∷ Γ) G (subst (λ z → Form z (α > β)) h₁₁ (lam α (subst (λ z → Form z β) (cong (_∷_ α) h₁₂) (weak-i (α ∷ (Γ' ++ (u ∷ ε))) Γ (subst (λ z → Form z β) h₂ (weak-i (α ∷ Γ') Γ f))))))
 sub-weak-p-23-lam-2 {n} {u} {v} {α} {β} {Γ} Γ' f G .(Γ' ++ (u ∷ (v ∷ Γ))) refl h₁₂ h₂ = cong (lam α) (
  sub-weak-p-23-i (α ∷ Γ') f G (cong (_∷_ α) h₁₂) h₂)

 sub-weak-p-23-lam-1 : ∀ {n} → {u v α β : Type n} {Γ : Ctx n} (Γ' : Ctx n) (f : Form ((α ∷ Γ') ++ Γ) β) (G : Form (v ∷ Γ) u) →
  (h₁ : (Γ' ++ (u ∷ ε)) ++ (v ∷ Γ) ≡ Γ' ++ (u ∷ (v ∷ Γ))) →
  (Γ'' : Ctx n) →
  (h₂₁ : Γ'' ≡ (Γ' ++ (u ∷ ε)) ++ Γ) →
  (h₂₂ : Γ' ++ (u ∷ Γ) ≡ Γ'') →
  lam α (weak-i (α ∷ Γ') Γ f) ≡
  sub-i Γ' (v ∷ Γ) G (subst (λ z → Form z (α > β)) h₁ (weak-i (Γ' ++ (u ∷ ε)) Γ (subst (λ z → Form z (α > β)) h₂₁ (lam α (subst (λ z → Form z β) (cong (λ z → α ∷ z) h₂₂) (weak-i (α ∷ Γ') Γ f))))))
 sub-weak-p-23-lam-1 {n} {u} {v} {α} {β} {Γ} Γ' f G h₁ .((Γ' ++ (u ∷ ε)) ++ Γ) refl h₂₂ = sub-weak-p-23-lam-2 Γ' f G ((Γ' ++ (u ∷ ε)) ++ (v ∷ Γ)) h₁ refl (cong (_∷_ α) h₂₂)

 sub-weak-p-23-i : ∀ {n} → {t u v : Type n} {Γ : Ctx n} (Γ' : Ctx n) (F : Form (Γ' ++ Γ) t) (G : Form (v ∷ Γ) u) →
  (h₁ : (Γ' ++ (u ∷ ε)) ++ (v ∷ Γ) ≡ Γ' ++ (u ∷ (v ∷ Γ))) →
  (h₂ : Γ' ++ (u ∷ Γ) ≡ (Γ' ++ (u ∷ ε)) ++ Γ) →
  weak-i Γ' Γ F ≡ sub-i Γ' (v ∷ Γ) G (subst (λ z → Form z t) h₁ (weak-i (Γ' ++ (u ∷ ε)) Γ (subst (λ z → Form z t) h₂ (weak-i Γ' Γ F))))
-- sub-weak-p-23-i {_} {.(lookup-Var (Γ' ++ Γ) x)} {u} {v} {Γ} Γ' (var x) G h₁ h₂ = {!!}
 sub-weak-p-23-i {_} {β} {u} {v} {Γ} Γ' (var x p) G h₁ h₂ = sub-weak-p-23-var-1 Γ' x G p h₁ (Γ' ++ (u ∷ Γ)) h₂ refl (trans (weak-var-p Γ' Γ x) p)
 sub-weak-p-23-i {_} {.($o > $o)} {u} {v} {Γ} Γ' N G h₁ h₂ = erase-subst (Ctx _) (λ z → Form z ($o > $o)) N (Γ' ++ (u ∷ Γ)) ((Γ' ++ (u ∷ ε)) ++ Γ) h₂ (λ z → N ≡ sub-i Γ' (v ∷ Γ) G (subst (λ z → Form z ($o > $o)) h₁ (weak-i (Γ' ++ (u ∷ ε)) Γ z))) (erase-subst (Ctx _) (λ z → Form z ($o > $o)) N ((Γ' ++ (u ∷ ε)) ++ (v ∷ Γ)) (Γ' ++ (u ∷ (v ∷ Γ))) h₁ (λ z → N ≡ sub-i Γ' (v ∷ Γ) G z) refl)  -- rewrite h₂ | h₁ = refl
 sub-weak-p-23-i {_} {.($o > ($o > $o))} {u} {v} {Γ} Γ' A G h₁ h₂ = erase-subst (Ctx _) (λ z → Form z ($o > ($o > $o))) A (Γ' ++ (u ∷ Γ)) ((Γ' ++ (u ∷ ε)) ++ Γ) h₂ (λ z → A ≡ sub-i Γ' (v ∷ Γ) G (subst (λ z → Form z ($o > ($o > $o))) h₁ (weak-i (Γ' ++ (u ∷ ε)) Γ z))) (erase-subst (Ctx _) (λ z → Form z ($o > ($o > $o))) A ((Γ' ++ (u ∷ ε)) ++ (v ∷ Γ)) (Γ' ++ (u ∷ (v ∷ Γ))) h₁ (λ z → A ≡ sub-i Γ' (v ∷ Γ) G z) refl)  -- rewrite h₂ | h₁ = refl
 sub-weak-p-23-i {_} {((t > $o) > $o)} {u} {v} {Γ} Γ' Π G h₁ h₂ = erase-subst (Ctx _) (λ z → Form z ((t > $o) > $o)) Π (Γ' ++ (u ∷ Γ)) ((Γ' ++ (u ∷ ε)) ++ Γ) h₂ (λ z → Π ≡ sub-i Γ' (v ∷ Γ) G (subst (λ z → Form z ((t > $o) > $o)) h₁ (weak-i (Γ' ++ (u ∷ ε)) Γ z))) (erase-subst (Ctx _) (λ z → Form z ((t > $o) > $o)) Π ((Γ' ++ (u ∷ ε)) ++ (v ∷ Γ)) (Γ' ++ (u ∷ (v ∷ Γ))) h₁ (λ z → Π ≡ sub-i Γ' (v ∷ Γ) G z) refl)  -- rewrite h₂ | h₁ = refl
 sub-weak-p-23-i {_} {((t > $o) > .t)} {u} {v} {Γ} Γ' i G h₁ h₂ = erase-subst (Ctx _) (λ z → Form z ((t > $o) > t)) i (Γ' ++ (u ∷ Γ)) ((Γ' ++ (u ∷ ε)) ++ Γ) h₂ (λ z → i ≡ sub-i Γ' (v ∷ Γ) G (subst (λ z → Form z ((t > $o) > t)) h₁ (weak-i (Γ' ++ (u ∷ ε)) Γ z))) (erase-subst (Ctx _) (λ z → Form z ((t > $o) > t)) i ((Γ' ++ (u ∷ ε)) ++ (v ∷ Γ)) (Γ' ++ (u ∷ (v ∷ Γ))) h₁ (λ z → i ≡ sub-i Γ' (v ∷ Γ) G z) refl)  -- rewrite h₂ | h₁ = refl
 sub-weak-p-23-i {_} {t} {u} {v} {Γ} Γ' (app f₁ f₂) G h₁ h₂ = sub-weak-p-23-app-1 Γ' f₁ f₂ G h₁ (Γ' ++ (u ∷ Γ)) h₂ refl
 sub-weak-p-23-i {_} {α > β} {u} {v} {Γ} Γ' (lam .α f) G h₁ h₂ = sub-weak-p-23-lam-1 Γ' f G h₁ (Γ' ++ (u ∷ Γ)) h₂ refl


sub-weak-var-p-1-this-2 : ∀ {n} → {u v β : Type n} {Γ : Ctx n} (Γ' : Ctx n) (G : Form Γ u) →
 (Γ'' : Ctx n)
 (h₁ : β ∷ Γ'' ≡ β ∷ (Γ' ++ (v ∷ Γ)))
 (p' : β ≡ β) →
 var this refl ≡
 subst (λ z → Form z β) h₁ (var this p')
sub-weak-var-p-1-this-2 {n} {u} {v} {β} {Γ} Γ' G ._ refl refl = refl

sub-weak-var-p-1-this-1 : ∀ {n} → {u v β : Type n} {Γ : Ctx n} (Γ' : Ctx n) (G : Form Γ u) →
 (h₁ : β ∷ ((Γ' ++ (v ∷ ε)) ++ Γ) ≡ β ∷ (Γ' ++ (v ∷ Γ)))
 (Γ'' : Ctx n)
 (h₂ : β ∷ Γ'' ≡ β ∷ ((Γ' ++ (v ∷ ε)) ++ (u ∷ Γ)))
 (p' : lookup-Var ((β ∷ (Γ' ++ (v ∷ ε))) ++ (u ∷ Γ)) (subst Var h₂ this) ≡ β) →
 var this refl ≡
 subst (λ z → Form z β) h₁ (sub-var (β ∷ (Γ' ++ (v ∷ ε))) Γ G (subst Var h₂ this) p')
sub-weak-var-p-1-this-1 {n} {u} {v} {β} {Γ} Γ' G h₁ ._ refl p' = sub-weak-var-p-1-this-2 Γ' G _ h₁ p'

mutual
 sub-weak-var-p-1-next-2 : ∀ {n} → {u v β t : Type n} {Γ : Ctx n} (Γ' : Ctx n) (x : Var (Γ' ++ Γ)) (G : Form Γ u) →
  (p : lookup-Var (Γ' ++ (v ∷ Γ)) (weak-var Γ' Γ x) ≡ β)
  (Γ'' : Ctx n)
  (h₁₁ : t ∷ Γ'' ≡ t ∷ (Γ' ++ (v ∷ Γ)))
  (h₁₂ : ((Γ' ++ (v ∷ ε)) ++ Γ) ≡ Γ'')
  (h₂ : (Γ' ++ (v ∷ (u ∷ Γ))) ≡ ((Γ' ++ (v ∷ ε)) ++ (u ∷ Γ)))
  (p' : lookup-Var ((Γ' ++ (v ∷ ε)) ++ (u ∷ Γ)) (subst Var h₂ (weak-var Γ' (u ∷ Γ) (weak-var Γ' Γ x))) ≡ β) →
  var (next (weak-var Γ' Γ x)) p ≡
  subst (λ z → Form z β) h₁₁ (weak-i ε Γ'' (subst (λ z → Form z β) h₁₂ (sub-var (Γ' ++ (v ∷ ε)) Γ G (subst Var h₂ (weak-var Γ' (u ∷ Γ) (weak-var Γ' Γ x))) p')))
 sub-weak-var-p-1-next-2 {n} {u} {v} {β} {t} {Γ} Γ' x G p ._ refl h₁₂ h₂ p' = 
  subst (λ z → var (next {_} {t} (weak-var Γ' Γ x)) p ≡ weak-i ε (Γ' ++ (v ∷ Γ)) z)
   (sub-weak-var-p-1 Γ' x G p h₁₂ h₂ p')
   refl

 sub-weak-var-p-1-next-1 : ∀ {n} → {u v β t : Type n} {Γ : Ctx n} (Γ' : Ctx n) (x : Var (Γ' ++ Γ)) (G : Form Γ u) →
  (p : lookup-Var (Γ' ++ (v ∷ Γ)) (weak-var Γ' Γ x) ≡ β)
  (h₁ : t ∷ ((Γ' ++ (v ∷ ε)) ++ Γ) ≡ t ∷ (Γ' ++ (v ∷ Γ)))
  (Γ'' : Ctx n)
  (h₂₁ : t ∷ Γ'' ≡ t ∷ ((Γ' ++ (v ∷ ε)) ++ (u ∷ Γ)))
  (h₂₂ : (Γ' ++ (v ∷ (u ∷ Γ))) ≡ Γ'')
  (p' : lookup-Var (t ∷ ((Γ' ++ (v ∷ ε)) ++ (u ∷ Γ))) (subst Var h₂₁ (next (subst Var h₂₂ (weak-var Γ' (u ∷ Γ) (weak-var Γ' Γ x))))) ≡ β) →
  var (next (weak-var Γ' Γ x)) p ≡
  subst (λ z → Form z β) h₁ (sub-var (t ∷ (Γ' ++ (v ∷ ε))) Γ G (subst Var h₂₁ (next (subst Var h₂₂ (weak-var Γ' (u ∷ Γ) (weak-var Γ' Γ x))))) p')
 sub-weak-var-p-1-next-1 {n} {u} {v} {β} {t} {Γ} Γ' x G p h₁ ._ refl h₂₂ p' = sub-weak-var-p-1-next-2 Γ' x G p _ h₁ refl h₂₂ p'

 sub-weak-var-p-1 : ∀ {n} → {u v β : Type n} {Γ : Ctx n} (Γ' : Ctx n) (x : Var (Γ' ++ Γ)) (G : Form Γ u) →
  (p : lookup-Var (Γ' ++ (v ∷ Γ)) (weak-var Γ' Γ x) ≡ β) →
  (h₁ : (Γ' ++ (v ∷ ε)) ++ Γ ≡ Γ' ++ (v ∷ Γ)) →
  (h₂ : Γ' ++ (v ∷ (u ∷ Γ)) ≡ (Γ' ++ (v ∷ ε)) ++ (u ∷ Γ)) →
  (p' : lookup-Var ((Γ' ++ (v ∷ ε)) ++ (u ∷ Γ)) (subst Var h₂ (weak-var Γ' (u ∷ Γ) (weak-var Γ' Γ x))) ≡ β) →
  var (weak-var Γ' Γ x) p ≡
  subst (λ z → Form z β) h₁ (sub-var (Γ' ++ (v ∷ ε)) Γ G (subst Var h₂ (weak-var Γ' (u ∷ Γ) (weak-var Γ' Γ x))) p')
 sub-weak-var-p-1 ε x G refl refl refl refl = refl
 sub-weak-var-p-1 {n} {u} {v} {β} {Γ} (.β ∷ Γ') this G refl h₁ h₂ p' = sub-weak-var-p-1-this-1 Γ' G h₁ _ h₂ p'
 sub-weak-var-p-1 {n} {u} {v} {β} {Γ} (t ∷ Γ') (next x) G p h₁ h₂ p' = sub-weak-var-p-1-next-1 Γ' x G p h₁ _ h₂ refl p'

sub-weak-p-1-var : ∀ {n} → {u v β : Type n} {Γ : Ctx n} (Γ' : Ctx n) (x : Var (Γ' ++ Γ)) (G : Form Γ u) →
 (p : lookup-Var (Γ' ++ Γ) x ≡ β)
 (h₁ : (Γ' ++ (v ∷ ε)) ++ Γ ≡ Γ' ++ (v ∷ Γ))
 (Γ'' : Ctx n)
 (h₂₁ : Γ'' ≡ (Γ' ++ (v ∷ ε)) ++ (u ∷ Γ))
 (h₂₂ : Γ' ++ (v ∷ (u ∷ Γ)) ≡ Γ'')
 (p' : lookup-Var Γ'' (subst Var h₂₂ (weak-var Γ' (u ∷ Γ) (weak-var Γ' Γ x))) ≡ β) →
 var (weak-var Γ' Γ x) (trans (weak-var-p Γ' Γ x) p) ≡
 subst (λ z → Form z β) h₁ (sub-i (Γ' ++ (v ∷ ε)) Γ G (subst (λ z → Form z β) h₂₁ (var (subst Var h₂₂ (weak-var Γ' (u ∷ Γ) (weak-var Γ' Γ x))) p')))
sub-weak-p-1-var {n} {u} {v} {β} {Γ} Γ' x G p h₁ ._ refl h₂₂ p' = sub-weak-var-p-1 Γ' x G (trans (weak-var-p Γ' Γ x) p) h₁ h₂₂ p'

mutual
 sub-weak-p-1-app-2 : ∀ {n} → {t u v w : Type n} {Γ : Ctx n} (Γ' : Ctx n) (f₁ : Form (Γ' ++ Γ) (w > t)) (f₂ : Form (Γ' ++ Γ) w) (G : Form Γ u) →
  (Γ'' : Ctx n) →
  (h₁₁ : Γ'' ≡ Γ' ++ (v ∷ Γ)) →
  (h₁₂ : (Γ' ++ (v ∷ ε)) ++ Γ ≡ Γ'') →
  (h₂ : Γ' ++ (v ∷ (u ∷ Γ)) ≡ (Γ' ++ (v ∷ ε)) ++ (u ∷ Γ)) →
  app (weak-i Γ' Γ f₁) (weak-i Γ' Γ f₂) ≡
  subst (λ z → Form z t) h₁₁ (app (subst (λ z → Form z (w > t)) h₁₂ (sub-i (Γ' ++ (v ∷ ε)) Γ G (subst (λ z → Form z (w > t)) h₂ (weak-i Γ' (u ∷ Γ) (weak-i Γ' Γ f₁))))) (subst (λ z → Form z w) h₁₂ (sub-i (Γ' ++ (v ∷ ε)) Γ G (subst (λ z → Form z w) h₂ (weak-i Γ' (u ∷ Γ) (weak-i Γ' Γ f₂))))))
 sub-weak-p-1-app-2 {n} {t} {u} {v} {w} {Γ} Γ' f₁ f₂ G .(Γ' ++ (v ∷ Γ)) refl h₁₂ h₂ = 
  trans (cong (λ z → app z (weak-i Γ' Γ f₂)) (
    sub-weak-p-1-i Γ' f₁ G h₁₂ h₂
   ))
   (cong (λ z → app (subst (λ z → Form z (w > t)) h₁₂ (sub-i (Γ' ++ (v ∷ ε)) Γ G (subst (λ z → Form z (w > t)) h₂ (weak-i Γ' (u ∷ Γ) (weak-i Γ' Γ f₁))))) z) (
    sub-weak-p-1-i Γ' f₂ G h₁₂ h₂
   ))

 sub-weak-p-1-app-1 : ∀ {n} → {t u v w : Type n} {Γ : Ctx n} (Γ' : Ctx n) (f₁ : Form (Γ' ++ Γ) (w > t)) (f₂ : Form (Γ' ++ Γ) w) (G : Form Γ u) →
  (h₁ : (Γ' ++ (v ∷ ε)) ++ Γ ≡ Γ' ++ (v ∷ Γ)) →
  (Γ'' : Ctx n) →
  (h₂₁ : Γ'' ≡ (Γ' ++ (v ∷ ε)) ++ (u ∷ Γ)) →
  (h₂₂ : Γ' ++ (v ∷ (u ∷ Γ)) ≡ Γ'') →
  app (weak-i Γ' Γ f₁) (weak-i Γ' Γ f₂) ≡
  subst (λ z → Form z t) h₁ (sub-i (Γ' ++ (v ∷ ε)) Γ G (subst (λ z → Form z t) h₂₁ (app (subst (λ z → Form z (w > t)) h₂₂ (weak-i Γ' (u ∷ Γ) (weak-i Γ' Γ f₁))) (subst (λ z → Form z w) h₂₂ (weak-i Γ' (u ∷ Γ) (weak-i Γ' Γ f₂))))))
 sub-weak-p-1-app-1 {n} {t} {u} {v} {w} {Γ} Γ' f₁ f₂ G h₁ .((Γ' ++ (v ∷ ε)) ++ (u ∷ Γ)) refl h₂₂ = sub-weak-p-1-app-2 Γ' f₁ f₂ G ((Γ' ++ (v ∷ ε)) ++ Γ) h₁ refl h₂₂

 sub-weak-p-1-lam-2 : ∀ {n} → {u v α β : Type n} {Γ : Ctx n} (Γ' : Ctx n) (f : Form ((α ∷ Γ') ++ Γ) β) (G : Form Γ u) →
  (Γ'' : Ctx n) →
  (h₁₁ : Γ'' ≡ Γ' ++ (v ∷ Γ)) →
  (h₁₂ : (Γ' ++ (v ∷ ε)) ++ Γ ≡ Γ'') →
  (h₂ : Γ' ++ (v ∷ (u ∷ Γ)) ≡ (Γ' ++ (v ∷ ε)) ++ (u ∷ Γ)) →
  lam α (weak-i (α ∷ Γ') Γ f) ≡
  subst (λ z → Form z (α > β)) h₁₁ (lam α (subst (λ z → Form z β) (cong (_∷_ α) h₁₂) (sub-i (α ∷ (Γ' ++ (v ∷ ε))) Γ G (subst (λ z → Form z β) (cong (_∷_ α) h₂) (weak-i (α ∷ Γ') (u ∷ Γ) (weak-i (α ∷ Γ') Γ f))))))
 sub-weak-p-1-lam-2 {n} {u} {v} {α} {β} {Γ} Γ' f G .(Γ' ++ (v ∷ Γ)) refl h₁₂ h₂ = cong (lam α) (
  sub-weak-p-1-i (α ∷ Γ') f G (cong (_∷_ α) h₁₂) (cong (_∷_ α) h₂))

 sub-weak-p-1-lam-1 : ∀ {n} → {u v α β : Type n} {Γ : Ctx n} (Γ' : Ctx n) (f : Form ((α ∷ Γ') ++ Γ) β) (G : Form Γ u) →
  (h₁ : (Γ' ++ (v ∷ ε)) ++ Γ ≡ Γ' ++ (v ∷ Γ)) →
  (Γ'' : Ctx n) →
  (h₂₁ : Γ'' ≡ (Γ' ++ (v ∷ ε)) ++ (u ∷ Γ)) →
  (h₂₂ : Γ' ++ (v ∷ (u ∷ Γ)) ≡ Γ'') →
  lam α (weak-i (α ∷ Γ') Γ f) ≡
  subst (λ z → Form z (α > β)) h₁ (sub-i (Γ' ++ (v ∷ ε)) Γ G (subst (λ z → Form z (α > β)) h₂₁ (lam α (subst (λ z → Form z β) (cong (λ z → α ∷ z) h₂₂) (weak-i (α ∷ Γ') (u ∷ Γ) (weak-i (α ∷ Γ') Γ f))))))
 sub-weak-p-1-lam-1 {n} {u} {v} {α} {β} {Γ} Γ' f G h₁ .((Γ' ++ (v ∷ ε)) ++ (u ∷ Γ)) refl h₂₂ = sub-weak-p-1-lam-2 Γ' f G ((Γ' ++ (v ∷ ε)) ++ Γ) h₁ refl h₂₂

 sub-weak-p-1-i : ∀ {n} → {t u v : Type n} {Γ : Ctx n} (Γ' : Ctx n) (F : Form (Γ' ++ Γ) t) (G : Form Γ u) →
   (h₁ : (Γ' ++ (v ∷ ε)) ++ Γ ≡ Γ' ++ (v ∷ Γ)) →
   (h₂ : Γ' ++ (v ∷ (u ∷ Γ)) ≡ (Γ' ++ (v ∷ ε)) ++ (u ∷ Γ)) →
   weak-i Γ' Γ F ≡ subst (λ z → Form z t) h₁ (sub-i (Γ' ++ (v ∷ ε)) Γ G (subst (λ z → Form z t) h₂ (weak-i Γ' (u ∷ Γ) (weak-i Γ' Γ F))))
 sub-weak-p-1-i {_} {β} {u} {v} {Γ} Γ' (var x p) G h₁ h₂ = sub-weak-p-1-var Γ' x G p h₁ _ h₂ refl (trans (weak-var-p Γ' (u ∷ Γ) (weak-var Γ' Γ x)) (trans (weak-var-p Γ' Γ x) p))
 sub-weak-p-1-i {_} {$o > $o} {u} {v} {Γ} Γ' N G h₁ h₂ = erase-subst (Ctx _) (λ z → Form z ($o > $o)) N (Γ' ++ (v ∷ (u ∷ Γ))) ((Γ' ++ (v ∷ ε)) ++ (u ∷ Γ)) h₂ (λ z → N ≡ subst (λ z → Form z ($o > $o)) h₁ (sub-i (Γ' ++ (v ∷ ε)) Γ G z)) (erase-subst (Ctx _) (λ z → Form z ($o > $o)) N ((Γ' ++ (v ∷ ε)) ++ Γ) (Γ' ++ (v ∷ Γ)) h₁ (λ z → N ≡ z) refl)  -- rewrite h₂ | h₁ = refl
 sub-weak-p-1-i {_} {$o > ($o > $o)} {u} {v} {Γ} Γ' A G h₁ h₂ = erase-subst (Ctx _) (λ z → Form z ($o > ($o > $o))) A (Γ' ++ (v ∷ (u ∷ Γ))) ((Γ' ++ (v ∷ ε)) ++ (u ∷ Γ)) h₂ (λ z → A ≡ subst (λ z → Form z ($o > ($o > $o))) h₁ (sub-i (Γ' ++ (v ∷ ε)) Γ G z)) (erase-subst (Ctx _) (λ z → Form z ($o > ($o > $o))) A ((Γ' ++ (v ∷ ε)) ++ Γ) (Γ' ++ (v ∷ Γ)) h₁ (λ z → A ≡ z) refl)  -- rewrite h₂ | h₁ = refl
 sub-weak-p-1-i {_} {(t > $o) > $o} {u} {v} {Γ} Γ' Π G h₁ h₂ = erase-subst (Ctx _) (λ z → Form z ((t > $o) > $o)) Π (Γ' ++ (v ∷ (u ∷ Γ))) ((Γ' ++ (v ∷ ε)) ++ (u ∷ Γ)) h₂ (λ z → Π ≡ subst (λ z → Form z ((t > $o) > $o)) h₁ (sub-i (Γ' ++ (v ∷ ε)) Γ G z)) (erase-subst (Ctx _) (λ z → Form z ((t > $o) > $o)) Π ((Γ' ++ (v ∷ ε)) ++ Γ) (Γ' ++ (v ∷ Γ)) h₁ (λ z → Π ≡ z) refl)  -- rewrite h₂ | h₁ = refl
 sub-weak-p-1-i {_} {(t > $o) > .t} {u} {v} {Γ} Γ' i G h₁ h₂ = erase-subst (Ctx _) (λ z → Form z ((t > $o) > t)) i (Γ' ++ (v ∷ (u ∷ Γ))) ((Γ' ++ (v ∷ ε)) ++ (u ∷ Γ)) h₂ (λ z → i ≡ subst (λ z → Form z ((t > $o) > t)) h₁ (sub-i (Γ' ++ (v ∷ ε)) Γ G z)) (erase-subst (Ctx _) (λ z → Form z ((t > $o) > t)) i ((Γ' ++ (v ∷ ε)) ++ Γ) (Γ' ++ (v ∷ Γ)) h₁ (λ z → i ≡ z) refl)  -- rewrite h₂ | h₁ = refl
 sub-weak-p-1-i {_} {t} {u} {v} {Γ} Γ' (app f₁ f₂) G h₁ h₂ = sub-weak-p-1-app-1 Γ' f₁ f₂ G h₁ (Γ' ++ (v ∷ (u ∷ Γ))) h₂ refl
 sub-weak-p-1-i {_} {α > β} {u} {v} {Γ} Γ' (lam .α f) G h₁ h₂ = sub-weak-p-1-lam-1 Γ' f G h₁ (Γ' ++ (v ∷ (u ∷ Γ))) h₂ refl


sub-weak-p-1'-var : ∀ {n} → {t u : Type n} {Γ : Ctx n} (Γ' : Ctx n) (x : Var (Γ' ++ Γ)) (G : Form Γ u)
 (p : lookup-Var (Γ' ++ Γ) x ≡ t) →
 var x p ≡ sub-var Γ' Γ G (weak-var Γ' Γ x) (trans (weak-var-p Γ' Γ x) p)
sub-weak-p-1'-var ε x G p = refl
sub-weak-p-1'-var (v ∷ Γ') this G p = refl
sub-weak-p-1'-var {_} {_} {_} {Γ} (v ∷ Γ') (next x) G p = 
 subst (λ z → var (next {_} {v} x) p ≡ weak-i ε (Γ' ++ Γ) z)
  (sub-weak-p-1'-var Γ' x G p)
  refl

sub-weak-p-1'-i : ∀ {n} → {t u : Type n} {Γ : Ctx n} (Γ' : Ctx n) (F : Form (Γ' ++ Γ) t) (G : Form Γ u) →
  F ≡ sub-i Γ' Γ G (weak-i Γ' Γ F)
sub-weak-p-1'-i Γ' (var x p) G = sub-weak-p-1'-var Γ' x G p
sub-weak-p-1'-i Γ' N G = refl
sub-weak-p-1'-i Γ' A G = refl
sub-weak-p-1'-i Γ' Π G = refl
sub-weak-p-1'-i Γ' i G = refl
sub-weak-p-1'-i {_} {_} {_} {Γ} Γ' (app f₁ f₂) G = trans (cong (λ z → app z f₂) (sub-weak-p-1'-i Γ' f₁ G)) ((cong (λ z → app (sub-i Γ' Γ G (weak-i Γ' Γ f₁)) z) (sub-weak-p-1'-i Γ' f₂ G)))
sub-weak-p-1'-i Γ' (lam α f) G = cong (lam α) (sub-weak-p-1'-i (α ∷ Γ') f G)


sub-weak-p-1 : ∀ {n} → {t u v : Type n} {Γ : Ctx n} (F : Form Γ t) (G : Form Γ u) →
  weak-i ε Γ F ≡ sub-i (v ∷ ε) Γ G (weak-i ε (u ∷ Γ) (weak-i ε Γ F))
sub-weak-p-1 F G = sub-weak-p-1-i ε F G refl refl

sub-weak-p-23 : ∀ {n} → {t u v : Type n} {Γ : Ctx n} (F : Form Γ t) (G : Form (v ∷ Γ) u) →
 weak-i ε Γ F ≡ sub-i ε (v ∷ Γ) G (weak-i (u ∷ ε) Γ (weak-i ε Γ F))
sub-weak-p-23 F G = sub-weak-p-23-i ε F G refl refl

sub-weak-p-1' : ∀ {n} → {t u : Type n} {Γ : Ctx n} (F : Form Γ t) (G : Form Γ u) →
  F ≡ sub G (weak F)
sub-weak-p-1' F G = sub-weak-p-1'-i ε F G

-- --------------------------

weak-var-irr-proof-2 : ∀ {n} {Γ : Ctx n} (t : Type n) (x : Var Γ)
 (p₁ : lookup-Var Γ x ≡ t)
 (p₂ : lookup-Var Γ x ≡ t) →
 var x p₁ ≡ var x p₂
weak-var-irr-proof-2 {n} {Γ} .(lookup-Var Γ x) x refl refl = refl

weak-var-irr-proof : ∀ {n} {Γ : Ctx n} (t : Type n) (x₁ x₂ : Var Γ)
 (p₁ : lookup-Var Γ x₁ ≡ t)
 (p₂ : lookup-Var Γ x₂ ≡ t) →
 x₁ ≡ x₂ →
 var x₁ p₁ ≡ var x₂ p₂
weak-var-irr-proof {n} {Γ} t .x₂ x₂ p₁ p₂ refl = weak-var-irr-proof-2 t x₂ p₁ p₂  -- rewrite h = weak-var-irr-proof-2 t x₂ p₁ p₂

-- --------------------------

weak-weak-var-p-1-this : ∀ {n} Γ₁ Γ₂ → (t u v w : Type n)
 (Γ'₁ Γ'₂ : Ctx n) →
 (h₁ : w ∷ Γ'₁ ≡ w ∷ ((Γ₂ ++ (t ∷ ε)) ++ Γ₁))
 (h₂ : w ∷ Γ'₂ ≡ w ∷ ((Γ₂ ++ (t ∷ ε)) ++ (u ∷ Γ₁))) →
 weak-var (w ∷ (Γ₂ ++ (t ∷ ε))) Γ₁ (subst Var h₁ this) ≡
 subst Var h₂ this
weak-weak-var-p-1-this Γ₁ Γ₂ t u v w ._ ._ refl refl = refl

mutual
 weak-weak-var-p-1-next : ∀ {n} Γ₁ Γ₂ → (t u v w : Type n) (x : Var (Γ₂ ++ Γ₁))
  (Γ'₁ Γ'₂ : Ctx n) →
  (h₁₁ : w ∷ Γ'₁ ≡ w ∷ ((Γ₂ ++ (t ∷ ε)) ++ Γ₁))
  (h₁₂ : Γ₂ ++ (t ∷ Γ₁) ≡ Γ'₁)
  (h₂₁ : w ∷ Γ'₂ ≡ w ∷ ((Γ₂ ++ (t ∷ ε)) ++ (u ∷ Γ₁)))
  (h₂₂ : Γ₂ ++ (t ∷ (u ∷ Γ₁)) ≡ Γ'₂) →
  weak-var (w ∷ (Γ₂ ++ (t ∷ ε))) Γ₁ (subst Var h₁₁ (next (subst Var h₁₂ (weak-var Γ₂ Γ₁ x)))) ≡
  subst Var h₂₁ (next (subst Var h₂₂ (weak-var Γ₂ (u ∷ Γ₁) (weak-var Γ₂ Γ₁ x))))
 weak-weak-var-p-1-next Γ₁ Γ₂ t u v w x ._ ._ refl h₁₂ refl h₂₂ = cong next (weak-weak-var-p-1 Γ₁ Γ₂ t u v x h₁₂ h₂₂)

 weak-weak-var-p-1 : ∀ {n} Γ₁ Γ₂ → (t u v : Type n) (x : Var (Γ₂ ++ Γ₁))
  (h₁ : Γ₂ ++ (t ∷ Γ₁) ≡ (Γ₂ ++ (t ∷ ε)) ++ Γ₁)
  (h₂ : Γ₂ ++ (t ∷ (u ∷ Γ₁)) ≡ (Γ₂ ++ (t ∷ ε)) ++ (u ∷ Γ₁)) →
  weak-var (Γ₂ ++ (t ∷ ε)) Γ₁ (subst Var h₁ (weak-var Γ₂ Γ₁ x)) ≡
  subst Var h₂ (weak-var Γ₂ (u ∷ Γ₁) (weak-var Γ₂ Γ₁ x))
 weak-weak-var-p-1 Γ₂ ε t u v x refl refl = refl
 weak-weak-var-p-1 Γ₁ (w ∷ Γ₂) t u v this h₁ h₂ = weak-weak-var-p-1-this Γ₁ Γ₂ t u v w _ _ h₁ h₂
 weak-weak-var-p-1 Γ₁ (w ∷ Γ₂) t u v (next x) h₁ h₂ = weak-weak-var-p-1-next Γ₁ Γ₂ t u v w x _ _ h₁ refl h₂ refl

weak-weak-p-1-var : ∀ {n} Γ₁ Γ₂ → (t u v : Type n) (x : Var (Γ₂ ++ Γ₁))
 (Γ'₁ Γ'₂ : Ctx n) →
 (h₁₁ : Γ'₁ ≡ (Γ₂ ++ (t ∷ ε)) ++ Γ₁) →
 (h₁₂ : Γ₂ ++ (t ∷ Γ₁) ≡ Γ'₁) →
 (h₂₁ : Γ'₂ ≡ (Γ₂ ++ (t ∷ ε)) ++ (u ∷ Γ₁)) →
 (h₂₂ : Γ₂ ++ (t ∷ (u ∷ Γ₁)) ≡ Γ'₂) →
 (p₁ : lookup-Var Γ'₁ (subst Var h₁₂ (weak-var Γ₂ Γ₁ x)) ≡ v)
 (p₂ : lookup-Var Γ'₂ (subst Var h₂₂ (weak-var Γ₂ (u ∷ Γ₁) (weak-var Γ₂ Γ₁ x))) ≡ v) →
 weak-i (Γ₂ ++ (t ∷ ε)) Γ₁ (subst (λ z → Form z v) h₁₁ (var (subst Var h₁₂ (weak-var Γ₂ Γ₁ x)) p₁)) ≡
 subst (λ z → Form z v) h₂₁ (var (subst Var h₂₂ (weak-var Γ₂ (u ∷ Γ₁) (weak-var Γ₂ Γ₁ x))) p₂)
weak-weak-p-1-var Γ₁ Γ₂ t u v x .((Γ₂ ++ (t ∷ ε)) ++ Γ₁) .((Γ₂ ++ (t ∷ ε)) ++ (u ∷ Γ₁)) refl h₁₂ refl h₂₂ p₁ p₂ = weak-var-irr-proof _ (weak-var (Γ₂ ++ (t ∷ ε)) Γ₁ (subst Var h₁₂ (weak-var Γ₂ Γ₁ x))) (subst Var h₂₂ (weak-var Γ₂ (u ∷ Γ₁) (weak-var Γ₂ Γ₁ x))) (trans (weak-var-p (Γ₂ ++ (t ∷ ε)) Γ₁ (subst Var h₁₂ (weak-var Γ₂ Γ₁ x))) p₁) p₂ (weak-weak-var-p-1 Γ₁ Γ₂ t u v x h₁₂ h₂₂)

mutual
 weak-weak-p-1-app : ∀ {n} Γ₁ Γ₂ → (t u v α : Type n) (f₁ : Form (Γ₂ ++ Γ₁) (α > v)) (f₂ : Form (Γ₂ ++ Γ₁) α)
  (Γ'₁ Γ'₂ : Ctx n) →
  (h₁₁ : Γ'₁ ≡ (Γ₂ ++ (t ∷ ε)) ++ Γ₁) →
  (h₁₂ : Γ₂ ++ (t ∷ Γ₁) ≡ Γ'₁) →
  (h₂₁ : Γ'₂ ≡ (Γ₂ ++ (t ∷ ε)) ++ (u ∷ Γ₁)) →
  (h₂₂ : Γ₂ ++ (t ∷ (u ∷ Γ₁)) ≡ Γ'₂) →
  weak-i (Γ₂ ++ (t ∷ ε)) Γ₁ (subst (λ z → Form z v) h₁₁ (app (subst (λ z → Form z (α > v)) h₁₂ (weak-i Γ₂ Γ₁ f₁)) (subst (λ z → Form z α) h₁₂ (weak-i Γ₂ Γ₁ f₂)))) ≡
  subst (λ z → Form z v) h₂₁ (app (subst (λ z → Form z (α > v)) h₂₂ (weak-i Γ₂ (u ∷ Γ₁) (weak-i Γ₂ Γ₁ f₁))) (subst (λ z → Form z α) h₂₂ (weak-i Γ₂ (u ∷ Γ₁) (weak-i Γ₂ Γ₁ f₂))))
 weak-weak-p-1-app Γ₁ Γ₂ t u v α f₁ f₂ ._ ._ refl h₁₂ refl h₂₂ = 
  trans (cong (λ z → app z (weak-i (Γ₂ ++ (t ∷ ε)) Γ₁ (subst (λ z → Form z α) h₁₂ (weak-i Γ₂ Γ₁ f₂)))) (weak-weak-p-1-i Γ₁ Γ₂ t u (α > v) f₁ h₁₂ h₂₂)) (cong (app (subst (λ z → Form z (α > v)) h₂₂ (weak-i Γ₂ (u ∷ Γ₁) (weak-i Γ₂ Γ₁ f₁)))) (weak-weak-p-1-i Γ₁ Γ₂ t u α f₂ h₁₂ h₂₂))

 weak-weak-p-1-lam : ∀ {n} Γ₁ Γ₂ → (t u α β : Type n) (X : Form (α ∷ (Γ₂ ++ Γ₁)) β)
  (Γ'₁ Γ'₂ : Ctx n) →
  (h₁₁ : Γ'₁ ≡ (Γ₂ ++ (t ∷ ε)) ++ Γ₁) →
  (h₁₂ : Γ₂ ++ (t ∷ Γ₁) ≡ Γ'₁) →
  (h₂₁ : Γ'₂ ≡ (Γ₂ ++ (t ∷ ε)) ++ (u ∷ Γ₁)) →
  (h₂₂ : Γ₂ ++ (t ∷ (u ∷ Γ₁)) ≡ Γ'₂) →
  weak-i (Γ₂ ++ (t ∷ ε)) Γ₁ (subst (λ z → Form z (α > β)) h₁₁ (lam α (subst (λ z → Form z β) (cong (_∷_ α) h₁₂) (weak-i (α ∷ Γ₂) Γ₁ X)))) ≡
  subst (λ z → Form z (α > β)) h₂₁ (lam α (subst (λ z → Form z β) (cong (_∷_ α) h₂₂) (weak-i (α ∷ Γ₂) (u ∷ Γ₁) (weak-i (α ∷ Γ₂) Γ₁ X))))
 weak-weak-p-1-lam Γ₁ Γ₂ t u α β X .((Γ₂ ++ (t ∷ ε)) ++ Γ₁) .((Γ₂ ++ (t ∷ ε)) ++ (u ∷ Γ₁)) refl h₁₂ refl h₂₂ = cong (lam α) (weak-weak-p-1-i Γ₁ (α ∷ Γ₂) t u β X (cong (_∷_ α) h₁₂) (cong (_∷_ α) h₂₂))

 weak-weak-p-1-i : ∀ {n} Γ₁ Γ₂ → (t u v : Type n) (X : Form (Γ₂ ++ Γ₁) v) →
  (h₁ : Γ₂ ++ (t ∷ Γ₁) ≡ (Γ₂ ++ (t ∷ ε)) ++ Γ₁) →
  (h₂ : Γ₂ ++ (t ∷ (u ∷ Γ₁)) ≡ (Γ₂ ++ (t ∷ ε)) ++ (u ∷ Γ₁)) →
  weak-i {n} {v} {u} (Γ₂ ++ (t ∷ ε)) Γ₁ (subst (λ z → Form z v) h₁ (weak-i {n} {v} {t} Γ₂ Γ₁ X)) ≡ subst (λ z → Form z v) h₂ (weak-i {n} {v} {t} Γ₂ (u ∷ Γ₁) (weak-i {n} {v} {u} Γ₂ Γ₁ X))
 weak-weak-p-1-i Γ₁ Γ₂ t u v (var x p) h₁ h₂ = weak-weak-p-1-var Γ₁ Γ₂ t u v x _ _ h₁ refl h₂ refl (trans (weak-var-p Γ₂ Γ₁ x) p) (trans (weak-var-p Γ₂ (u ∷ Γ₁) (weak-var Γ₂ Γ₁ x)) (trans (weak-var-p Γ₂ Γ₁ x) p))
 weak-weak-p-1-i Γ₁ Γ₂ t u .($o > $o) N h₁ h₂ = erase-subst (Ctx _) (λ z → Form z ($o > $o)) N (Γ₂ ++ (t ∷ (u ∷ Γ₁))) ((Γ₂ ++ (t ∷ ε)) ++ (u ∷ Γ₁)) h₂ (λ z → weak-i (Γ₂ ++ (t ∷ ε)) Γ₁ (subst (λ z → Form z ($o > $o)) h₁ N) ≡ z) (erase-subst (Ctx _) (λ z → Form z ($o > $o)) N (Γ₂ ++ (t ∷ Γ₁)) ((Γ₂ ++ (t ∷ ε)) ++ Γ₁) h₁ (λ z → weak-i {_} {_} {u} (Γ₂ ++ (t ∷ ε)) Γ₁ z ≡ N) refl)  -- rewrite h₂ | h₁ = refl
 weak-weak-p-1-i Γ₁ Γ₂ t u .($o > ($o > $o)) A h₁ h₂ = erase-subst (Ctx _) (λ z → Form z ($o > ($o > $o))) A (Γ₂ ++ (t ∷ (u ∷ Γ₁))) ((Γ₂ ++ (t ∷ ε)) ++ (u ∷ Γ₁)) h₂ (λ z → weak-i (Γ₂ ++ (t ∷ ε)) Γ₁ (subst (λ z → Form z ($o > ($o > $o))) h₁ A) ≡ z) (erase-subst (Ctx _) (λ z → Form z ($o > ($o > $o))) A (Γ₂ ++ (t ∷ Γ₁)) ((Γ₂ ++ (t ∷ ε)) ++ Γ₁) h₁ (λ z → weak-i {_} {_} {u} (Γ₂ ++ (t ∷ ε)) Γ₁ z ≡ A) refl)  -- rewrite h₂ | h₁ = refl
 weak-weak-p-1-i Γ₁ Γ₂ t u .((α > $o) > $o) (Π {._} {α}) h₁ h₂ = erase-subst (Ctx _) (λ z → Form z ((α > $o) > $o)) Π (Γ₂ ++ (t ∷ (u ∷ Γ₁))) ((Γ₂ ++ (t ∷ ε)) ++ (u ∷ Γ₁)) h₂ (λ z → weak-i (Γ₂ ++ (t ∷ ε)) Γ₁ (subst (λ z → Form z ((α > $o) > $o)) h₁ Π) ≡ z) (erase-subst (Ctx _) (λ z → Form z ((α > $o) > $o)) Π (Γ₂ ++ (t ∷ Γ₁)) ((Γ₂ ++ (t ∷ ε)) ++ Γ₁) h₁ (λ z → weak-i {_} {_} {u} (Γ₂ ++ (t ∷ ε)) Γ₁ z ≡ Π) refl)  -- rewrite h₂ | h₁ = refl
 weak-weak-p-1-i Γ₁ Γ₂ t u .((α > $o) > α) (i {._} {α}) h₁ h₂ = erase-subst (Ctx _) (λ z → Form z ((α > $o) > α)) i (Γ₂ ++ (t ∷ (u ∷ Γ₁))) ((Γ₂ ++ (t ∷ ε)) ++ (u ∷ Γ₁)) h₂ (λ z → weak-i (Γ₂ ++ (t ∷ ε)) Γ₁ (subst (λ z → Form z ((α > $o) > α)) h₁ i) ≡ z) (erase-subst (Ctx _) (λ z → Form z ((α > $o) > α)) i (Γ₂ ++ (t ∷ Γ₁)) ((Γ₂ ++ (t ∷ ε)) ++ Γ₁) h₁ (λ z → weak-i {_} {_} {u} (Γ₂ ++ (t ∷ ε)) Γ₁ z ≡ i) refl)  -- rewrite h₂ | h₁ = refl
 weak-weak-p-1-i Γ₁ Γ₂ t u v (app f₁ f₂) h₁ h₂ = weak-weak-p-1-app Γ₁ Γ₂ t u v _ f₁ f₂ _ _ h₁ refl h₂ refl
 weak-weak-p-1-i Γ₁ Γ₂ t u .(α > β) (lam {._} {β} α f) h₁ h₂ = weak-weak-p-1-lam Γ₁ Γ₂ t u α β f _ _ h₁ refl h₂ refl

weak-weak-p-1 : ∀ {n} Γ → (t u v : Type n) (X : Form Γ v) →
  weak-i {n} {v} {u} (t ∷ ε) Γ (weak-i {n} {v} {t} ε Γ X) ≡ weak-i {n} {v} {t} ε (u ∷ Γ) (weak-i {n} {v} {u} ε Γ X)
weak-weak-p-1 Γ t u v X = weak-weak-p-1-i Γ ε t u v X refl refl

-- -----------------------


thevar : ∀ {n Γ} → (Γ' : Ctx n) (α : Type n) → Var (Γ' ++ (α ∷ Γ))
thevar ε α = this
thevar (β ∷ Γ') α = next (thevar Γ' α)

occurs-p-2-i-var : ∀ {n} {Γ : Ctx n} {α β : Type n} (Γ' : Ctx n)
 (v : Var (Γ' ++ Γ))
 (p : lookup-Var (Γ' ++ Γ) v ≡ β) →
 eq-Var (thevar Γ' α) (weak-var Γ' Γ v) ≡ false
occurs-p-2-i-var ε v p = refl
occurs-p-2-i-var (γ ∷ Γ') this p = refl
occurs-p-2-i-var (γ ∷ Γ') (next v) p = occurs-p-2-i-var Γ' v p

occurs-p-2-i : ∀ {n} {Γ : Ctx n} {α β : Type n} (Γ' : Ctx n) (F : Form (Γ' ++ Γ) β) →
 occurs {n} {Γ' ++ (α ∷ Γ)} (thevar Γ' α) (weak-i Γ' Γ F) ≡ false
occurs-p-2-i Γ' (var v p) = occurs-p-2-i-var Γ' v p
occurs-p-2-i Γ' N = refl
occurs-p-2-i Γ' A = refl
occurs-p-2-i Γ' Π = refl
occurs-p-2-i Γ' i = refl
occurs-p-2-i {n} {Γ} {α} {β} Γ' (app f₁ f₂) = subst (λ z → z ∨ occurs (thevar Γ' α) (weak-i Γ' Γ f₂) ≡ false) (sym (occurs-p-2-i {n} {Γ} {α} {_ > β} Γ' f₁)) (occurs-p-2-i {n} {Γ} {α} Γ' f₂)  -- rewrite occurs-p-2-i {n} {Γ} {α} {_ > β} Γ' f₁ | occurs-p-2-i {n} {Γ} {α} Γ' f₂ = refl
occurs-p-2-i Γ' (lam γ f) = occurs-p-2-i (γ ∷ Γ') f


occurs-p-2 : ∀ {n} {Γ : Ctx n} {α β : Type n} (F : Form Γ β) →
 occurs {n} {α ∷ Γ} this (weak F) ≡ false
occurs-p-2 F = occurs-p-2-i ε F

-- -----------------------

sub-sub-weak-weak-p-3-i-var-2-this : ∀ {n} → {Γ Γ' : Ctx n} {α β γ : Type n} →
 (Γ1 Γ2 : Ctx n) →
 (eq1 : γ ∷ Γ1 ≡ γ ∷ (Γ' ++ (α ∷ (α ∷ Γ)))) →
 (eq2 : γ ∷ Γ2 ≡ γ ∷ (Γ' ++ (α ∷ Γ))) →
 (p1 : lookup-Var (γ ∷ (Γ' ++ (α ∷ (α ∷ Γ)))) (subst Var eq1 this) ≡ β) →
 (p2 : lookup-Var (γ ∷ (Γ' ++ (α ∷ Γ))) (subst Var eq2 this) ≡ β) →
 sub-var (γ ∷ Γ') (α ∷ Γ) (var this refl) (subst Var eq1 this) p1 ≡ var (subst Var eq2 this) p2
sub-sub-weak-weak-p-3-i-var-2-this {n} {Γ} {Γ'} {α} .(Γ' ++ (α ∷ (α ∷ Γ))) .(Γ' ++ (α ∷ Γ)) refl refl refl refl = refl

mutual
 sub-sub-weak-weak-p-3-i-var-2-next : ∀ {n} → {Γ Γ' : Ctx n} {α β γ : Type n}
  (x : Var ((Γ' ++ (α ∷ ε)) ++ Γ)) →
  (Γ1 Γ2 : Ctx n) →
  (eq1 : γ ∷ Γ1 ≡ γ ∷ (Γ' ++ (α ∷ (α ∷ Γ)))) →
  (eq12 : (Γ' ++ (α ∷ ε)) ++ (α ∷ Γ) ≡ Γ1) →
  (eq2 : γ ∷ Γ2 ≡ γ ∷ (Γ' ++ (α ∷ Γ))) →
  (eq22 : (Γ' ++ (α ∷ ε)) ++ Γ ≡ Γ2) →
  (p1 : lookup-Var ((γ ∷ Γ') ++ (lookup-Var (α ∷ Γ) this ∷ (α ∷ Γ))) (subst Var eq1 (next (subst Var eq12 (weak-var (Γ' ++ (α ∷ ε)) Γ x)))) ≡ β) →
  (p2 : lookup-Var (γ ∷ (Γ' ++ (α ∷ Γ))) (subst Var eq2 (next (subst Var eq22 x))) ≡ β) →
  sub-var (γ ∷ Γ') (α ∷ Γ) (var this refl) (subst Var eq1 (next (subst Var eq12 (weak-var (Γ' ++ (α ∷ ε)) Γ x)))) p1
  ≡ var (subst Var eq2 (next (subst Var eq22 x))) p2
 sub-sub-weak-weak-p-3-i-var-2-next {n} {Γ} {Γ'} {α} x .(Γ' ++ (α ∷ (α ∷ Γ))) .(Γ' ++ (α ∷ Γ)) refl eq12 refl eq22 p1 p2 = cong (weak-i ε (Γ' ++ (α ∷ Γ))) (sub-sub-weak-weak-p-3-i-var-2 {n} {Γ} {Γ'} {α} x eq12 eq22 p1 p2)

 sub-sub-weak-weak-p-3-i-var-2 : ∀ {n} → {Γ Γ' : Ctx n} {α β : Type n} (x : Var ((Γ' ++ (α ∷ ε)) ++ Γ)) →
  (eq1 : (Γ' ++ (α ∷ ε)) ++ (α ∷ Γ) ≡ Γ' ++ (α ∷ (α ∷ Γ))) →
  (eq2 : (Γ' ++ (α ∷ ε)) ++ Γ ≡ Γ' ++ (α ∷ Γ)) →
  (p1 : lookup-Var (Γ' ++ (α ∷ (α ∷ Γ))) (subst Var eq1 (weak-var (Γ' ++ (α ∷ ε)) Γ x)) ≡ β) →
  (p2 : lookup-Var (Γ' ++ (α ∷ Γ)) (subst Var eq2 x) ≡ β) →
  sub-var Γ' (α ∷ Γ) (var this refl) (subst Var eq1 (weak-var (Γ' ++ (α ∷ ε)) Γ x)) p1
  ≡ var (subst Var eq2 x) p2
 sub-sub-weak-weak-p-3-i-var-2 {n} {Γ} {ε} this refl refl refl refl = refl
 sub-sub-weak-weak-p-3-i-var-2 {n} {Γ} {ε} (next x) refl refl refl refl = refl
 sub-sub-weak-weak-p-3-i-var-2 {n} {Γ} {γ ∷ Γ'} this eq1 eq2 p1 p2 = sub-sub-weak-weak-p-3-i-var-2-this {n} {Γ} {Γ'} {_} {_} {γ} ((Γ' ++ (_ ∷ ε)) ++ (_ ∷ Γ)) ((Γ' ++ (_ ∷ ε)) ++ Γ) eq1 eq2 p1 p2
 sub-sub-weak-weak-p-3-i-var-2 {n} {Γ} {γ ∷ Γ'} (next x) eq1 eq2 p1 p2 = sub-sub-weak-weak-p-3-i-var-2-next {n} {Γ} {Γ'} {_} {_} {γ} x ((Γ' ++ (_ ∷ ε)) ++ (_ ∷ Γ)) ((Γ' ++ (_ ∷ ε)) ++ Γ) eq1 refl eq2 refl p1 p2

sub-sub-weak-weak-p-3-i-var : ∀ {n} → {Γ Γ' : Ctx n} {α β : Type n} (x : Var ((Γ' ++ (α ∷ ε)) ++ Γ)) →
 (Γ1 Γ2 : Ctx n) →
 (eq11 : Γ1 ≡ Γ' ++ (α ∷ (α ∷ Γ))) →
 (eq12 : (Γ' ++ (α ∷ ε)) ++ (α ∷ Γ) ≡ Γ1) →
 (eq21 : Γ2 ≡ Γ' ++ (α ∷ Γ)) →
 (eq22 : (Γ' ++ (α ∷ ε)) ++ Γ ≡ Γ2) →
 (p1 : lookup-Var Γ1 (subst Var eq12 (weak-var (Γ' ++ (α ∷ ε)) Γ x)) ≡ β) →
 (p2 : lookup-Var Γ2 (subst Var eq22 x) ≡ β) →
 sub-i Γ' (α ∷ Γ) (var this refl) (subst (λ z → Form z β) eq11 (var (subst Var eq12 (weak-var (Γ' ++ (α ∷ ε)) Γ x)) p1))
 ≡ subst (λ z → Form z β) eq21 (var (subst Var eq22 x) p2)
sub-sub-weak-weak-p-3-i-var {n} {Γ} {Γ'} {α} x .(Γ' ++ (α ∷ (α ∷ Γ))) .(Γ' ++ (α ∷ Γ)) refl eq12 refl eq22 p1 p2 = sub-sub-weak-weak-p-3-i-var-2 {n} {Γ} {Γ'} {α} x eq12 eq22 p1 p2

mutual
 sub-sub-weak-weak-p-3-i-app : ∀ {n} → {Γ Γ' : Ctx n} {α β γ : Type n}
  (f₁ : Form ((Γ' ++ (α ∷ ε)) ++ Γ) (γ > β)) →
  (f₂ : Form ((Γ' ++ (α ∷ ε)) ++ Γ) γ) →
  (Γ1 Γ2 : Ctx n) →
  (eq1 : Γ1 ≡ Γ' ++ (α ∷ (α ∷ Γ))) →
  (eq12 : (Γ' ++ (α ∷ ε)) ++ (α ∷ Γ) ≡ Γ1) →
  (eq2 : Γ2 ≡ Γ' ++ (α ∷ Γ)) →
  (eq22 : (Γ' ++ (α ∷ ε)) ++ Γ ≡ Γ2) →
  sub-i Γ' (α ∷ Γ) (var this refl) (subst (λ z → Form z β) eq1 (app (subst (λ z → Form z (γ > β)) eq12 (weak-i (Γ' ++ (α ∷ ε)) Γ f₁)) (subst (λ z → Form z γ) eq12 (weak-i (Γ' ++ (α ∷ ε)) Γ f₂))))
  ≡ subst (λ z → Form z β) eq2 (app (subst (λ z → Form z (γ > β)) eq22 f₁) (subst (λ z → Form z γ) eq22 f₂))
 sub-sub-weak-weak-p-3-i-app {n} {Γ} {Γ'} {α} {β} {γ} f₁ f₂ .(Γ' ++ (α ∷ (α ∷ Γ))) .(Γ' ++ (α ∷ Γ)) refl eq12 refl eq22 = trans (cong (λ z → app z (sub-i Γ' (α ∷ Γ) (var this refl) (subst (λ z → Form z γ) eq12 (weak-i (Γ' ++ (α ∷ ε)) Γ f₂)))) (sub-sub-weak-weak-p-3-i {n} {Γ} {Γ'} {α} {γ > β} f₁ eq12 eq22)) (cong (app (subst (λ z → Form z (γ > β)) eq22 f₁)) (sub-sub-weak-weak-p-3-i {n} {Γ} {Γ'} {α} {γ} f₂ eq12 eq22))

 sub-sub-weak-weak-p-3-i-lam : ∀ {n} → {Γ Γ' : Ctx n} {α β γ : Type n}
  (f : Form (γ ∷ ((Γ' ++ (α ∷ ε)) ++ Γ)) β)
  (Γ1 Γ2 : Ctx n)
  (eq1 : Γ1 ≡ Γ' ++ (α ∷ (α ∷ Γ)))
  (eq12 : γ ∷ ((Γ' ++ (α ∷ ε)) ++ (α ∷ Γ)) ≡ γ ∷ Γ1)
  (eq2 : Γ2 ≡ Γ' ++ (α ∷ Γ))
  (eq22 : γ ∷ ((Γ' ++ (α ∷ ε)) ++ Γ) ≡ γ ∷ Γ2) →
  sub-i Γ' (α ∷ Γ) (var this refl) (subst (λ z → Form z (γ > β)) eq1 (lam γ (subst (λ z → Form z β) eq12 (weak-i (γ ∷ (Γ' ++ (α ∷ ε))) Γ f))))
  ≡ subst (λ z → Form z (γ > β)) eq2 (lam γ (subst (λ z → Form z β) eq22 f))
 sub-sub-weak-weak-p-3-i-lam {n} {Γ} {Γ'} {α} {β} {γ} f .(Γ' ++ (α ∷ (α ∷ Γ))) .(Γ' ++ (α ∷ Γ)) refl eq12 refl eq22 = cong (lam γ) (sub-sub-weak-weak-p-3-i {n} {Γ} {γ ∷ Γ'} {α} {β} f eq12 eq22)

 sub-sub-weak-weak-p-3-i : ∀ {n} → {Γ Γ' : Ctx n} {α β : Type n} (G : Form ((Γ' ++ (α ∷ ε)) ++ Γ) β) →
  (eq1 : (Γ' ++ (α ∷ ε)) ++ (α ∷ Γ) ≡ Γ' ++ (α ∷ (α ∷ Γ))) →
  (eq2 : (Γ' ++ (α ∷ ε)) ++ Γ ≡ Γ' ++ (α ∷ Γ)) →
  sub-i Γ' (α ∷ Γ) (var this refl) (subst (λ z → Form z β) eq1 (weak-i (Γ' ++ (α ∷ ε)) Γ G)) ≡ subst (λ z → Form z β) eq2 G
 sub-sub-weak-weak-p-3-i {n} {Γ} {Γ'} {α} {β} (var x p) eq1 eq2 = sub-sub-weak-weak-p-3-i-var {n} {Γ} {Γ'} {α} {β} x ((Γ' ++ (α ∷ ε)) ++ (α ∷ Γ)) ((Γ' ++ (α ∷ ε)) ++ Γ) eq1 refl eq2 refl (trans (weak-var-p (Γ' ++ (α ∷ ε)) Γ x) p) p
 sub-sub-weak-weak-p-3-i {_} {Γ} {Γ'} {α} {$o > $o} N eq1 eq2 = erase-subst (Ctx _) (λ z → Form z ($o > $o)) N ((Γ' ++ (α ∷ ε)) ++ Γ) (Γ' ++ (α ∷ Γ)) eq2 (λ z → sub-i Γ' (α ∷ Γ) (var this refl) (subst (λ z → Form z ($o > $o)) eq1 N) ≡ z) (erase-subst (Ctx _) (λ z → Form z ($o > $o)) N ((Γ' ++ (α ∷ ε)) ++ (α ∷ Γ)) (Γ' ++ (α ∷ (α ∷ Γ))) eq1 (λ z → sub-i Γ' (α ∷ Γ) (var this refl) z ≡ N) refl)  -- rewrite eq2 | eq1 = refl
 sub-sub-weak-weak-p-3-i {_} {Γ} {Γ'} {α} {$o > ($o > $o)} A eq1 eq2 = erase-subst (Ctx _) (λ z → Form z ($o > ($o > $o))) A ((Γ' ++ (α ∷ ε)) ++ Γ) (Γ' ++ (α ∷ Γ)) eq2 (λ z → sub-i Γ' (α ∷ Γ) (var this refl) (subst (λ z → Form z ($o > ($o > $o))) eq1 A) ≡ z) (erase-subst (Ctx _) (λ z → Form z ($o > ($o > $o))) A ((Γ' ++ (α ∷ ε)) ++ (α ∷ Γ)) (Γ' ++ (α ∷ (α ∷ Γ))) eq1 (λ z → sub-i Γ' (α ∷ Γ) (var this refl) z ≡ A) refl)  -- rewrite eq2 | eq1 = refl
 sub-sub-weak-weak-p-3-i {_} {Γ} {Γ'} {α} {(β > $o) > $o} Π eq1 eq2 = erase-subst (Ctx _) (λ z → Form z ((β > $o) > $o)) Π ((Γ' ++ (α ∷ ε)) ++ Γ) (Γ' ++ (α ∷ Γ)) eq2 (λ z → sub-i Γ' (α ∷ Γ) (var this refl) (subst (λ z → Form z ((β > $o) > $o)) eq1 Π) ≡ z) (erase-subst (Ctx _) (λ z → Form z ((β > $o) > $o)) Π ((Γ' ++ (α ∷ ε)) ++ (α ∷ Γ)) (Γ' ++ (α ∷ (α ∷ Γ))) eq1 (λ z → sub-i Γ' (α ∷ Γ) (var this refl) z ≡ Π) refl)  -- rewrite eq2 | eq1 = refl
 sub-sub-weak-weak-p-3-i {_} {Γ} {Γ'} {α} {(β > $o) > .β} i eq1 eq2 = erase-subst (Ctx _) (λ z → Form z ((β > $o) > β)) i ((Γ' ++ (α ∷ ε)) ++ Γ) (Γ' ++ (α ∷ Γ)) eq2 (λ z → sub-i Γ' (α ∷ Γ) (var this refl) (subst (λ z → Form z ((β > $o) > β)) eq1 i) ≡ z) (erase-subst (Ctx _) (λ z → Form z ((β > $o) > β)) i ((Γ' ++ (α ∷ ε)) ++ (α ∷ Γ)) (Γ' ++ (α ∷ (α ∷ Γ))) eq1 (λ z → sub-i Γ' (α ∷ Γ) (var this refl) z ≡ i) refl)  -- rewrite eq2 | eq1 = refl
 sub-sub-weak-weak-p-3-i {_} {Γ} {Γ'} {α} (app f₁ f₂) eq1 eq2 = sub-sub-weak-weak-p-3-i-app {_} {Γ} {Γ'} {α} f₁ f₂ ((Γ' ++ (α ∷ ε)) ++ (α ∷ Γ)) ((Γ' ++ (α ∷ ε)) ++ Γ) eq1 refl eq2 refl
 sub-sub-weak-weak-p-3-i {_} {Γ} {Γ'} {α} (lam γ f) eq1 eq2 = sub-sub-weak-weak-p-3-i-lam {_} {Γ} {Γ'} {α} f ((Γ' ++ (α ∷ ε)) ++ (α ∷ Γ)) ((Γ' ++ (α ∷ ε)) ++ Γ) eq1 refl eq2 refl

sub-sub-weak-weak-p-3 : ∀ {n} → {Γ : Ctx n} {α β : Type n} (G : Form (α ∷ Γ) β) →
 sub (var this refl) (weak-i (α ∷ ε) Γ G) ≡ G
sub-sub-weak-weak-p-3 G = sub-sub-weak-weak-p-3-i {_} {_} {ε} G refl refl


sub-sub-weak-weak-p : ∀ {n} → {Γ : Ctx n} {α β : Type n} (F : Form Γ β) (G : Form (α ∷ Γ) β) →
 sub (var this refl) (sub-i (α ∷ (α ∷ ε)) Γ F (weak-i (α ∷ ε) (β ∷ Γ) (weak-i (α ∷ ε) Γ G))) ≡ G
sub-sub-weak-weak-p {_} {Γ} {α} {β} F G = subst (λ z → sub (var this refl) z ≡ G) (sub-weak-p-1-i (α ∷ ε) G F refl refl) (sub-sub-weak-weak-p-3 G)

sub-sub-weak-weak-p-2 : ∀ {n} → {Γ : Ctx n} {α β : Type n} (F G : Form (α ∷ Γ) β) →
 sub (var this refl) (sub-i (α ∷ (α ∷ ε)) Γ (lam α G) (weak-i (α ∷ ε) ((α > β) ∷ Γ) (weak-i (α ∷ ε) Γ F))) ≡ F
sub-sub-weak-weak-p-2 {_} {Γ} {α} {β} F G = subst (λ z → sub (var this refl) z ≡ F) (sub-weak-p-1-i (α ∷ ε) F (lam α G) refl refl) (sub-sub-weak-weak-p-3 F)

-- ----------------

mutual
 headNorm : {n : ℕ} {Γ : Ctx n} {α : Type n} → ℕ → Form Γ α → Form Γ α
-- headNorm m (app (app (lam α (lam _ (app Π (lam (_ > $o) (app (app A (app N (app (var this _) (var (next (next this)) _)))) (app (var this _) (var (next this) _))))))) F) G) = ?
 headNorm m (app F G) = headNorm' m (headNorm m F) G
 headNorm _ F = F

 headNorm' : {n : ℕ} {Γ : Ctx n} {α β : Type n} → ℕ → Form Γ (α > β) → Form Γ α → Form Γ β
 headNorm' (suc m) (lam _ F) G = headNorm m (sub G F)
 headNorm' 0 (lam _ F) G = app (lam _ F) G
 headNorm' _ F G = app F G

-- ----------------

!'[_]_ : ∀ {n} → {Γ : Ctx n} → (α : Type n) → Form Γ (α > $o) → Form Γ $o
!'[ α ] F = app Π F

infix 25 !'[_]_

?'[_]_ : ∀ {n} → {Γ : Ctx n} → (α : Type n) → Form Γ (α > $o) → Form Γ $o
?'[ α ] F = ?[ α ] (weak F · $ this {refl})

infix 25 ?'[_]_

ι' : ∀ {n} → {Γ : Ctx n} → (α : Type n) → Form Γ (α > $o) → Form Γ α
ι' α F = app i F


