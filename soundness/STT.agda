module STT where

-- simple type theory

{-
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Data.Nat hiding (_>_)
-}

open import StdLibStuff

open import Syntax


-- inference system

data ⊢_ : ∀ {n} → {Γ : Ctx n} → Form Γ $o → Set where
 ax-1 : ∀ {n} → {Γ : Ctx n} {x : Var Γ} →
  (p : lookup-Var Γ x ≡ $o) →
  ⊢ ((var x p || var x p) => var x p)

 ax-2 : ∀ {n} → {Γ : Ctx n} {x y : Var Γ} →
  (px : lookup-Var Γ x ≡ $o) →
  (py : lookup-Var Γ y ≡ $o) →
  ⊢ (var x px => (var x px || var y py))

 ax-3 : ∀ {n} → {Γ : Ctx n} {x y : Var Γ} →
  (px : lookup-Var Γ x ≡ $o) →
  (py : lookup-Var Γ y ≡ $o) →
  ⊢ ((var x px || var y py) => (var y py || var x px))

 ax-4 : ∀ {n} → {Γ : Ctx n} {x y z : Var Γ} →
  (px : lookup-Var Γ x ≡ $o) →
  (py : lookup-Var Γ y ≡ $o) →
  (pz : lookup-Var Γ z ≡ $o) →
  ⊢ ((var x px => var y py) => ((var z pz || var x px) => (var z pz || var y py)))

 ax-5 : ∀ {n} → {Γ : Ctx n} {α : Type n} {x y : Var Γ} →
  (px : lookup-Var Γ x ≡ α > $o) →
  (py : lookup-Var Γ y ≡ α) →
  ⊢ (app Π (var x px) => app (var x px) (var y py))

 ax-6 : ∀ {n} → {Γ : Ctx n} {α : Type n} {x y : Var Γ} →
  (px : lookup-Var Γ x ≡ α > $o) →
  (py : lookup-Var Γ y ≡ $o) →
  ⊢ ((![ α ] (weak (var y py) || app (weak (var x px)) (var this refl))) => (var y py || app Π (var x px)))

 ax-10-a : ∀ {n} → {Γ : Ctx n} {x y : Var Γ} →
  (px : lookup-Var Γ x ≡ $o) →
  (py : lookup-Var Γ y ≡ $o) →
  ⊢ ((var x px <=> var y py) => (var x px == var y py))

 ax-10-b : ∀ {n} → {Γ : Ctx n} {α β : Type n} {f g : Var Γ} →
  (pf : lookup-Var Γ f ≡ α > β) →
  (pg : lookup-Var Γ g ≡ α > β) →
  ⊢ ((![ α ] (app (weak (var f pf)) (var this refl) == app (weak (var g pg)) (var this refl))) => (var f pf == var g pg))

 ax-11 : ∀ {n} → {Γ : Ctx n} {α : Type n} {f : Var Γ} →
  (pf : lookup-Var Γ f ≡ α > $o) →
  ⊢ ((?[ α ] (app (weak (var f pf)) (var this refl))) => (app (var f pf) (app i (var f pf))))

 -- inf-I in Henkin is α-conversion
 -- with de Bruijn-indeces we need context extension instead
 extend-context : ∀ {n} {Γ : Ctx n} (α : Type n) {F : Form Γ $o} →
  ⊢_ {_} {α ∷ Γ} (weak F) →
  ⊢ F

 inf-II : ∀ {n} → (Γ Γ' : Ctx n) {α β : Type n} (F : Form (Γ' ++ Γ) β → Form Γ $o) (G : Form (α ∷ (Γ' ++ Γ)) β) (H : Form (Γ' ++ Γ) α) →
  ⊢ (F ((^[ α ] G) · H) => F (sub H G))  -- formulated as an inference rule in Henkin, as an axiom (containing expressions) here

 inf-III : ∀ {n} → (Γ Γ' : Ctx n) {α β : Type n} (F : Form (Γ' ++ Γ) β → Form Γ $o) (G : Form (α ∷ (Γ' ++ Γ)) β) (H : Form (Γ' ++ Γ) α) →
  ⊢ (F (sub H G) => F ((^[ α ] G) · H))  -- formulated as an inference rule in Henkin, as an axiom (containing expressions) here

 inf-IV : ∀ {n} → {Γ : Ctx n} {α : Type n} (F : Form Γ (α > $o)) (x : Var Γ) (G : Form Γ α) →
  occurs x F ≡ false →
  (p : lookup-Var Γ x ≡ α) →
  ⊢ (app F (var x p)) →
  ⊢ (app F G)

 inf-V : ∀ {n} → {Γ : Ctx n} {F G : Form Γ $o} →
  ⊢ (F => G) →   ⊢ F →
  ⊢ G

 inf-VI : ∀ {n} → {Γ : Ctx n} {α : Type n} {F : Form Γ (α > $o)} (x : Var Γ) →
  occurs x F ≡ false →
  (p : lookup-Var Γ x ≡ α) →
  ⊢ (app F (var x p) => app Π F)  -- formulated as an inference rule in Henkin, as an axiom (containing expressions) here

-- -------------------------


-- Variants of the axioms that are simpler to work with

ax-1-s : ∀ {n} → {Γ : Ctx n} {F : Form Γ $o} →
 ⊢ ((F || F) => F)

ax-2-s : ∀ {n} → {Γ : Ctx n} {F G : Form Γ $o} →
 ⊢ (F => (F || G))

ax-3-s : ∀ {n} → {Γ : Ctx n} {F G : Form Γ $o} →
 ⊢ ((F || G) => (G || F))

ax-4-s : ∀ {n} → {Γ : Ctx n} {F G H : Form Γ $o} →
 ⊢ ((F => G) => ((H || F) => (H || G)))

ax-5-s : ∀ {n} → {Γ : Ctx n} {α : Type n} (F : Form (α ∷ Γ) $o) (G : Form Γ α) →
  ⊢ (![ α ] F => sub G F)

ax-5-s2 : ∀ {n} → {Γ : Ctx n} {α : Type n} (F : Form Γ (α > $o)) (G : Form Γ α) →
  ⊢ ((![ α ] (~ (weak F · $ this {refl}))) => (~ (F · G)))

ax-5-s3 : ∀ {n} → {Γ : Ctx n} {α : Type n} (F : Form Γ (α > $o)) (G : Form Γ α) →
  ⊢ ((!'[ α ] F) => (F · G))

ax-6-s : ∀ {n} → {Γ : Ctx n} {α : Type n} {F : Form Γ $o} {G : Form (α ∷ Γ) $o} →
 ⊢ ((![ α ] (weak F || G)) => (F || (![ α ] G)))

ax-10-a-s : ∀ {n} → {Γ : Ctx n} {F G : Form Γ $o} →
 ⊢ ((F <=> G) => (F == G))

ax-10-b-s : ∀ {n} → {Γ : Ctx n} {α β : Type n} {F G : Form (α ∷ Γ) β} → ⊢ ((![ α ] (F == G)) => (^[ α ] F == ^[ α ] G))

ax-10-b-s2 : ∀ {n} → {Γ : Ctx n} {α β : Type n} {F G : Form Γ (α > β)} →
 ⊢ ((![ α ] (app (weak F) (var this refl) == app (weak G) (var this refl))) => (F == G))

ax-11-s : ∀ {n} → {Γ : Ctx n} {α : Type n} {F : Form (α ∷ Γ) $o} →
 ⊢ ((?[ α ] F => sub (ι α F) F))

ax-11-s2 : ∀ {n} → {Γ : Ctx n} {α : Type n} (F : Form Γ (α > $o)) →
 ⊢ ((?'[ α ] F) => (F · ι' α F))

inf-II-samectx : ∀ {n} → {Γ : Ctx n} {α β : Type n} (F : Form Γ β → Form Γ $o) (G : Form (α ∷ Γ) β) (H : Form Γ α) →
  ⊢ (F ((^[ α ] G) · H) => F (sub H G))
inf-II-samectx {_} {Γ} = inf-II Γ ε

inf-III-samectx : ∀ {n} → {Γ : Ctx n} {α β : Type n} (F : Form Γ β → Form Γ $o) (G : Form (α ∷ Γ) β) (H : Form Γ α) →
  ⊢ (F (sub H G) => F ((^[ α ] G) · H))
inf-III-samectx {_} {Γ} = inf-III Γ ε

inf-VI-s : ∀ {n} → {Γ : Ctx n} {α : Type n} {F : Form (α ∷ Γ) $o} →
 ⊢ F →
 ⊢ ![ α ] F

-- -------------------------


ax-5-s F G = inf-V (inf-II-samectx (λ z → (![ _ ] F) => z) F G) (subst (λ z → ⊢ ((![ _ ] F) => ((^[ _ ] F) · z))) (sym (sub-weak-p-1' G (^[ _ ] F))) (inf-V (inf-II-samectx (λ z → z) (app Π (var this refl) => app (var this refl) (weak G)) (^[ _ ] F)) (extend-context (_ > $o) (inf-IV _ this _ (occurs-p-2 (lam _ (weak G))) refl (inf-V (inf-III-samectx (λ z → z) (app Π (var this refl) => app (var this refl) (weak-i (_ ∷ ε) _ (weak G))) (var this refl)) (extend-context _ (inf-V (inf-II-samectx (λ z → z) (app Π (var (next (next this)) refl) => app (var (next (next this)) refl) (var this refl)) _) (inf-IV _ this _ refl refl (inf-V (inf-III-samectx (λ z → z) _ _) (ax-5 {_} {_} {_} {next this} {this} refl refl))))))))))


inf-VI-s {_} {Γ} {α} {F} = λ h → extend-context α (inf-V (inf-VI this (occurs-p-2 (lam α F)) refl) (inf-V (inf-III-samectx (λ z → z) (weak-i (α ∷ ε) Γ F) (var this refl)) (subst (λ z → ⊢ z) (sym (sub-sub-weak-weak-p-3 F)) h)))


ax-6-s {_} {Γ} {α} {F} {G} =
 subst (λ z → ⊢ ((![ α ] (weak F || z)) => (F || ![ α ] G))) (sub-sub-weak-weak-p F G)
 (inf-V (inf-II Γ (α ∷ ε) (λ z → ((![ α ] (weak F || z)) => (F || app Π (lam α G)))) (sub-i (α ∷ (α ∷ ε)) Γ F (weak-i (α ∷ ε) ($o ∷ Γ) (weak-i (α ∷ ε) Γ G))) (var this refl))
 (subst (λ z → ⊢ ((![ α ] (weak F || app (sub-i (α ∷ ε) Γ F (weak (weak (lam α G)))) (var this refl))) => (F || app Π z))) (sym (sub-weak-p-1' (lam α G) F))
 (inf-V (ax-5-s _ F) (inf-VI-s (inf-V (ax-5-s _ (weak (lam α G))) (inf-VI-s (ax-6 {_} {_} {α} {this} {next this} refl refl)))))))


ax-10-b-s {_} {Γ} {α} {β} {F} {G} =
 subst (λ z → ⊢ ((![ α ] (F == z) => (lam α F == lam α G)))) (sub-sub-weak-weak-p-3 G) (
 inf-V (inf-II Γ (α ∷ ε) (λ z → ((![ α ] (F == z)) => (lam α F == lam α G))) (weak-i (α ∷ ε) Γ G) (var this refl)) (
 subst (λ z → ⊢ ((![ α ] (z == app (weak (lam α G)) (var this refl))) => (lam α F == lam α G))) (sub-sub-weak-weak-p-2 F G) (
 inf-V (inf-II Γ (α ∷ ε) (λ z → (((![ α ] (z == app (weak (lam α G)) (var this refl)) => (lam α F == lam α G))))) (sub-i (α ∷ (α ∷ ε)) Γ (lam α G) (weak-i (α ∷ ε) ((α > β) ∷ Γ) (weak-i (α ∷ ε) Γ F))) (var this refl)) (
 subst (λ z → ⊢ (((![ α ] (app (sub-i (α ∷ ε) Γ (lam α G) (weak (weak (lam α F)))) (var this refl) == app (weak (lam α G)) (var this refl)) => (z == lam α G))))) (sym (sub-weak-p-1' (lam α F) (lam α G)))
 (inf-V (ax-5-s _ (lam α G)) (inf-VI-s (inf-V (ax-5-s _ (weak (lam α F))) (inf-VI-s (ax-10-b {_} {_} {α} {β} {this} {next this} refl refl)))))))))


ax-10-b-s2 {_} {Γ} {α} {β} {F} {G} =
 subst (λ z → (⊢ ((![ α ] (app (weak F) (var this refl) == app (weak G) (var this refl))) => (F == z)))) (sym (sub-weak-p-1' G F)) (
 subst (λ z → (⊢ ((![ α ] (app (weak F) (var this refl) == app z (var this refl))) => (F == sub F (weak G))))) (sym (sub-weak-p-1 G F)) (
 inf-V (ax-5-s ((![ α ] (app (weak (var this refl)) (var this refl) == app (weak (weak G)) (var this refl))) => (var this refl == weak G)) F) (
 inf-VI-s (
 inf-V (ax-5-s ((![ α ] (app (weak (var (next this) refl)) (var this refl) == app (weak (var this refl)) (var this refl))) => (var (next this) refl == var this refl)) (weak G)) (
 inf-VI-s (
 ax-10-b refl refl))))))


ax-11-s {_} {Γ} {α} {F} =
 subst (λ z → ⊢ ((?[ α ] z) => sub (app i (lam α F)) F)) (sub-sub-weak-weak-p-3 F) (
 inf-V (inf-II Γ (α ∷ ε) (λ z → ((?[ α ] z) => sub (app i (lam α F)) F)) (weak-i (α ∷ ε) Γ F) (var this refl)) (
 inf-V (inf-II Γ ε (λ z → ((?[ α ] app (weak (lam α F)) (var this refl)) => z)) F (app i (lam α F))) (
 inf-V (ax-5-s _ (lam α F)) (inf-VI-s (ax-11 {_} {_} {α} {this} refl)))))


ax-1-s {_} {_} {F} = inf-V (ax-5-s ((var this refl || var this refl) => var this refl) F) (inf-VI-s (ax-1 refl)) 


ax-2-s {_} {_} {F} {G} = subst (λ z → ⊢ (F => (F || z))) (sym (sub-weak-p-1' G F)) (inf-V (ax-5-s (var this refl => (var this refl || weak G)) F) (inf-VI-s (inf-V (ax-5-s (var (next this) refl => (var (next this) refl || var this refl)) (weak G)) (inf-VI-s (ax-2 refl refl)))))


ax-3-s {_} {_} {F} {G} = subst (λ z → ⊢ ((F || z) => (z || F))) (sym (sub-weak-p-1' G F)) (inf-V (ax-5-s _ F) (inf-VI-s (inf-V (ax-5-s _ (weak G)) (inf-VI-s (ax-3 {_} {_} {next this} {this} refl refl)))))


ax-4-s {_} {_} {F} {G} {H} = subst (λ z → ⊢ ((F => G) => ((z || F) => (z || G)))) (sym (sub-weak-p-1' H F)) (subst (λ z → ⊢ ((F => z) => ((sub F (weak H) || F) => (sub F (weak H) || z)))) (sym (sub-weak-p-1' G F)) (subst (λ z → ⊢ ((F => sub F (weak G)) => ((sub F z || F) => (sub F z || sub F (weak G))))) (sym (sub-weak-p-1' (weak H) (weak G))) (inf-V (ax-5-s _ F) (inf-VI-s (inf-V (ax-5-s _ (weak G)) (inf-VI-s (inf-V (ax-5-s _ (weak (weak H))) (inf-VI-s (ax-4 {_} {_} {next (next this)} {next this} {this} refl refl refl)))))))))


ax-10-a-s {_} {_} {F} {G} = subst (λ z → ⊢ ((F <=> z) => (F == z))) (sym (sub-weak-p-1' G F)) (inf-V (ax-5-s _ F) (inf-VI-s (inf-V (ax-5-s _ (weak G)) (inf-VI-s (ax-10-a {_} {_} {next this} {this} refl refl)))))


ax-5-s2 = λ F G → subst (λ z → ⊢ ((![ _ ] ~ (weak F · $ this {refl})) => ~ (z · G))) (sym (sub-weak-p-1' F G)) (ax-5-s (~ (weak F · $ this {refl})) G)


ax-5-s3 = λ F G →
 subst (λ z → ⊢ ((!'[ _ ] F) => (F · z))) (sym (sub-weak-p-1' G F)) (
 inf-V (ax-5-s ((!'[ _ ] ($ this {refl})) => (($ this {refl}) · weak G)) F) (
 inf-VI-s (
 inf-V (ax-5-s ((!'[ _ ] ($ (next this) {refl})) => (($ (next this) {refl}) · ($ this {refl}))) (weak G)) (
 inf-VI-s (
 ax-5 {_} {_} {_} {next this} {this} refl refl)))))


ax-11-s2 F =
 inf-V (ax-5-s ((?'[ _ ] ($ this {refl})) => (($ this {refl}) · ι' _ ($ this {refl}))) F) (
 inf-VI-s (
 ax-11 refl))


-- ----------------------------------

mutual
 hn-form : ∀ {n} → {Γ : Ctx n} {β : Type n} (F : Form Γ β → Form Γ $o) (G : Form Γ β) (m : ℕ) →
           ⊢ F (headNorm m G) → ⊢ F G
 hn-form F (app G H) m p = hn-form' F G H m (hn-form (λ z → F (headNorm' m z H)) G m p)
 hn-form F (var _ _) m p = p
 hn-form F N m p = p
 hn-form F A m p = p
 hn-form F Π m p = p
 hn-form F i m p = p
 hn-form F (lam _ _) m p = p

 hn-form' : ∀ {n} → {Γ : Ctx n} {α β : Type n} (F : Form Γ β → Form Γ $o) (G : Form Γ (α > β)) (H : Form Γ α) (m : ℕ) →
            ⊢ F (headNorm' m G H) → ⊢ F (app G H)
 hn-form' F (lam α G) H (suc m) p = inf-V (inf-III-samectx F G H) (hn-form F (sub H G) m p)
 hn-form' F (lam α G) H 0 p = p
 hn-form' F (var _ _) H zero p = p
 hn-form' F (var _ _) H (suc _) p = p
 hn-form' F N H zero p = p
 hn-form' F N H (suc _) p = p
 hn-form' F A H zero p = p
 hn-form' F A H (suc _) p = p
 hn-form' F Π H zero p = p
 hn-form' F Π H (suc _) p = p
 hn-form' F i H zero p = p
 hn-form' F i H (suc _) p = p
 hn-form' F (app _ _) H zero p = p
 hn-form' F (app _ _) H (suc _) p = p


