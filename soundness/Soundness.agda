module Soundness where

{-
open import Relation.Binary.PropositionalEquality
open import Data.Nat hiding (_>_)
-}

open import StdLibStuff

open import Syntax
open import STT
open import FSC
open import DerivedProps
open import HelpDefs


mutual
 sound : {n : ℕ} {Γ-t : Ctx n} (Γ : FSC-Ctx n Γ-t) (F : Form Γ-t $o) →
         Γ ⊢ F →
         ⊢ (hypos Γ F)
 sound Γ .(F || G) (or-I-l {F} {G} p) = inf-V (traverse-hypos F (F || G) Γ ax-2-s) (sound Γ F p)
 sound Γ .(F || G) (or-I-r {F} {G} p) = inf-V (traverse-hypos G (F || G) Γ (inf-V (inf-V ax-4-s ax-3-s) ax-2-s)) (sound Γ G p)
 sound Γ .(F & G) (&-I {F} {G} pF pG) = inf-V (inf-V (traverse-hypos-pair-I F G Γ) (sound Γ F pF)) (sound Γ G pG)
 sound Γ .(F => G) (=>-I {F} {G} p) = sound (F ∷h Γ) G p
 sound Γ .(~ F) (~-I {F} p) = inf-V (traverse-hypos (F => $false) (~ F) Γ (lem10 F)) (sound (F ∷h Γ) $false p)
 sound Γ .(![ t ] F) (!-I {t} {F} p) = traverse-=>-I-dep t F Γ (inf-VI-s (sound (t ∷ Γ) F p))
 sound Γ .(!'[ t ] F) (!'-I {t} {F} p) = traverse-=>-I-dep' t F Γ (sound (t ∷ Γ) (weak F · $ this {refl}) p)
 sound Γ F (elim x p) = inf-V (traverse-hypos-elim F Γ x) (sound-elim Γ (lookup-hyp Γ x) F p)
 sound Γ F (ac {t} p) = inf-V (traverse-hypos ((![ t > $o ] ((?[ t ] (var (next this) refl · var this refl)) => (var this refl · (ι t (var (next this) refl · var this refl))))) => F) F Γ (inf-V (lemb3 (![ t > $o ] ((?[ t ] (var (next this) refl · var this refl)) => (var this refl · ι t (var (next this) refl · var this refl)))) F) (inf-VI-s (ax-11-s {_} {(t > $o) ∷ _} {t} {var (next this) refl · var this refl})))) (sound-elim Γ (![ t > $o ] ((?[ t ] (var (next this) refl · var this refl)) => (var this refl · (ι t (var (next this) refl · var this refl))))) F p)
 sound Γ F (ac' {t} p) = inf-V (traverse-hypos ((![ t > $o ] ((?[ t ] ($ (next this) {refl} · $ this {refl})) => ($ this {refl} · ι' t ($ this {refl})))) => F) F Γ (inf-V (lemb3 (![ t > $o ] ((?[ t ] ($ (next this) {refl} · $ this {refl})) => ($ this {refl} · ι' t ($ this {refl})))) F) (inf-VI-s (ax-11-s2 ($ this {refl}))))) (sound-elim Γ (![ t > $o ] ((?[ t ] ($ (next this) {refl} · $ this {refl})) => ($ this {refl} · ι' t ($ this {refl})))) F p)
 sound Γ .(?[ t ] F) (?-I {t} {F} G p) = inf-V (traverse-hypos (sub G F) (?[ t ] F) Γ (inf-V ax-3-s (ax-5-s (~ F) G))) (sound Γ (sub G F) p)
 sound Γ .(?'[ t ] F) (?'-I {t} {F} G p) = inf-V (traverse-hypos (app F G) (?'[ t ] F) Γ (inf-V ax-3-s (ax-5-s2 F G))) (sound Γ (app F G) p)
 sound Γ .$true $true-I = traverse-hypos-use $true Γ (inf-VI-s (inf-V (inf-V ax-4-s ax-1-s) ax-2-s)) 
 sound Γ .(F == G) (==-I {t} {F} {G} p) = sound-== Γ t F G p
 sound Γ .(F ((^[ t ] G) · H)) (reduce {t} {u} {F} {G} {H} p) = inf-V (traverse-hypos (F (sub H G)) (F ((^[ t ] G) · H)) Γ (inf-III-samectx (λ x → (F x)) G H)) (sound Γ (F (sub H G)) p)
 sound Γ F (raa p) = inf-V (traverse-hypos (~ (~ F)) F Γ (lemb2 F)) (sound _ _ p)

 sound-elim : ∀ {n Γ-t} → (Γ : FSC-Ctx n Γ-t) (F G : Form Γ-t $o) →
  Γ , F ⊢ G →
  ⊢ (hypos Γ (F => G))
 sound-elim Γ F G (use p) = inf-V (traverse-hypos (G == F) (F => G) Γ (lem13 F G)) (sound-↔ Γ $o G F p)
 sound-elim Γ .(F & G) H (&-E-l {F} {G} p) = inf-V (traverse-hypos (F => H) ((F & G) => H) Γ (lem6 F G H)) (sound-elim Γ F H p)
 sound-elim Γ .(F & G) H (&-E-r {F} {G} p) = inf-V (traverse-hypos (G => H) ((F & G) => H) Γ (lem6b F G H)) (sound-elim Γ G H p)
 sound-elim Γ .(F => G) H (=>-E {F} {G} p₁ p₂) = inf-V (inf-V (traverse-hypos2 F (G => H) ((F => G) => H) Γ (lem7 F G H)) (sound Γ F p₁)) (sound-elim Γ G H p₂)
 sound-elim Γ .(~ F) H (~-E {F} p) = inf-V (traverse-hypos F (~ F => H) Γ (lemb4 F H)) (sound Γ F p)
 sound-elim Γ .(![ t ] F) H (!-E {t} {F} G p) = inf-V (traverse-hypos (sub G F => H) ((![ t ] F) => H) Γ (inf-V (lem9 (![ t ] F) (sub G F) H) (ax-5-s F G))) (sound-elim Γ (sub G F) H p)
 sound-elim Γ .(!'[ t ] F) H (!'-E {t} {F} G p) = inf-V (traverse-hypos ((F · G) => H) ((!'[ t ] F) => H) Γ (inf-V (lem9 (!'[ t ] F) (F · G) H) (ax-5-s3 F G))) (sound-elim Γ (F · G) H p)
 sound-elim Γ .$false H $false-E = traverse-hypos-use ($false => H) Γ (lem11 H)
 sound-elim Γ .(F || G) H (or-E {F} {G} p₁ p₂) = inf-V (inf-V (traverse-hypos2 (F => H) (G => H) ((F || G) => H) Γ (lemb5 F G H)) (sound _ _ p₁)) (sound _ _ p₂)
 sound-elim Γ .(?[ t ] F) H (?-E {t} {F} p) = inf-V (traverse-hypos (sub (ι t F) F => H) ((?[ t ] F) => H) Γ (inf-V (lem9 (?[ t ] F) (sub (ι t F) F) H) (ax-11-s {_} {_} {_} {F}))) (sound-elim Γ (sub (ι t F) F) H p)
 sound-elim Γ .(?'[ t ] F) H (?'-E {t} {F} p) = inf-V (traverse-hypos ((F · ι' _ F) => H) ((?'[ t ] F) => H) Γ (inf-V (lem9 (?'[ t ] F) (F · ι' t F) H) (ax-11-s2 F))) (sound-elim Γ (F · ι' _ F) H p)
 sound-elim Γ .(F ((^[ t ] G) · H)) I (reduce {t} {u} {F} {G} {H} p) = inf-V (traverse-hypos (F (sub H G) => I) (F ((^[ t ] G) · H) => I) Γ (inf-V (lem9 (F ((^[ t ] G) · H)) (F (sub H G)) I) (inf-II-samectx (λ x → (F x)) G H))) (sound-elim Γ (F (sub H G)) I p)
 sound-elim Γ .(F == G) H (r-bool-ext {F} {G} p) = inf-V (traverse-hypos (((F => G) & (G => F)) => H) ((F == G) => H) Γ (inf-V (lem9 (F == G) ((F => G) & (G => F)) H) (inf-V (lem2 (F == G) (F => G) (G => F)) (inf-V (inf-V (lemb1 ((F == G) => (F => G)) ((F == G) => (G => F))) (inf-V ax-3-s (inf-V (inf-V ax-4-s (inf-V (lem5 (F == G) (G == F)) (lem15 F G))) (inf-V ax-3-s (lem13 F G))))) (lem13 G F))))) (sound-elim Γ ((F => G) & (G => F)) H p)
 sound-elim Γ .(F == G) H (r-fun-ext {t} {u} {F} {G} I p) = inf-V (traverse-hypos (((F · I) == (G · I)) => H) ((F == G) => H) Γ (inf-V (lem9 (F == G) ((F · I) == (G · I)) H) (inf-V (inf-V (lem4 (F == G) (I == I) ((F · I) == (G · I))) (lem16 F G I I)) (lem12 I)))) (sound-elim Γ ((F · I) == (G · I)) H p)

 sound-== : ∀ {n Γ-t} → (Γ : FSC-Ctx n Γ-t) (t : Type n) (F G : Form Γ-t t) →
  Γ ⊢ t ∋ F == G →
  ⊢ (hypos Γ (F == G))
 sound-== Γ t F G (simp p) = sound-↔ Γ t F G p
 sound-== Γ t F G (step F' G' x p₁ p₂ p₃) = inf-V (inf-V (inf-V (traverse-hypos3 (F == F') (F' == G') (G' == G) (F == G) Γ (lem14 F F' G' G)) (sound-↔ Γ t F F' p₂)) (inf-V (traverse-hypos-elim (F' == G') Γ x) (sound-==-elim Γ (lookup-hyp Γ x) t F' G' p₁))) (sound-== Γ t G' G p₃)
 sound-== Γ .$o F G (bool-ext p) = inf-V (traverse-hypos ((F => G) & (G => F)) (F == G) Γ ax-10-a-s) (sound _ _ p)
 sound-== Γ .(t > u) F G (fun-ext {t} {u} p) = inf-V (traverse-hypos (![ t ] (((weak F) · $ this {refl}) == ((weak G) · $ this {refl}))) (F == G) Γ ax-10-b-s2) (traverse-=>-I-dep t ((weak F · $ this {refl}) == (weak G · $ this {refl})) Γ (inf-VI-s (sound-== (t ∷ Γ) u (weak F · $ this {refl}) (weak G · $ this {refl}) p)))


 sound-↔ : ∀ {n Γ-t} → (Γ : FSC-Ctx n Γ-t) (t : Type n) (F G : Form Γ-t t) →
  Γ ⊢ t ∋ F ↔ G →
  ⊢ (hypos Γ (F == G))
 sound-↔ Γ t .(var x p) .(var x p) (head-var ._ x p) = traverse-hypos-use (var x p == var x p) Γ (lem12 (var x p))
 sound-↔ Γ .t .c .c (head-const t c) = traverse-hypos-use (c == c) Γ (lem12 c)
 sound-↔ Γ .t₂ .(F₁ · G₁) .(F₂ · G₂) (head-app t₁ t₂ F₁ F₂ G₁ G₂ p₁ p₂) = inf-V (inf-V (traverse-hypos2 (F₁ == F₂) (G₁ == G₂) ((F₁ · G₁) == (F₂ · G₂)) Γ (lem16 F₁ F₂ G₁ G₂)) (sound-== Γ _ F₁ F₂ p₁)) (sound-== Γ _ G₁ G₂ p₂)
 sound-↔ Γ .(t₁ > t₂) .(lam t₁ F₁) .(lam t₁ F₂) (head-lam t₁ t₂ F₁ F₂ p) = traverse-hypos-eq-=>-I F₁ F₂ Γ (sound-== (t₁ ∷ Γ) t₂ F₁ F₂ p)
 sound-↔ Γ .(t₁ > t₂) .F₁ .(lam t₁ F₂) (head-lam-eta-left t₁ t₂ F₁ F₂ p) = inf-V (traverse-hypos (![ t₁ ] ((weak F₁ · $ this {refl}) == F₂)) (F₁ == lam t₁ F₂) Γ (inf-V (inf-V ax-4-s ax-10-b-s2) (subst (λ z → ⊢ ((![ t₁ ] ((weak F₁ · $ this {refl}) == z)) => (![ t₁ ] ((weak F₁ · $ this {refl}) == (weak (^[ t₁ ] F₂) · $ this {refl}))))) (sub-sub-weak-weak-p-3 F₂) (inf-III _ (t₁ ∷ ε) (λ z → ![ t₁ ] ((weak F₁ · $ this {refl}) == z)) (weak-i (t₁ ∷ ε) _ F₂) ($ this {refl}))))) (tst3' {_} {_} {ε} ((weak F₁ · $ this {refl}) == F₂) Γ refl (sound-== (t₁ ∷ Γ) t₂ (weak F₁ · $ this {refl}) F₂ p))
 sound-↔ Γ .(t₁ > t₂) .(lam t₁ F₂) .F₁ (head-lam-eta-right t₁ t₂ F₁ F₂ p) = inf-V (traverse-hypos (![ t₁ ] (F₂ == (weak F₁ · $ this {refl}))) (lam t₁ F₂ == F₁) Γ (inf-V (inf-V ax-4-s ax-10-b-s2) (subst (λ z → ⊢ ((![ t₁ ] (z == (weak F₁ · $ this {refl}))) => (![ t₁ ] ((weak (^[ t₁ ] F₂) · $ this {refl}) == (weak F₁ · $ this {refl}))))) (sub-sub-weak-weak-p-3 F₂) (inf-III _ (t₁ ∷ ε) (λ z → ![ t₁ ] (z == (weak F₁ · $ this {refl}))) (weak-i (t₁ ∷ ε) _ F₂) ($ this {refl}))))) (tst3' {_} {_} {ε} (F₂ == (weak F₁ · $ this {refl})) Γ refl (sound-== (t₁ ∷ Γ) t₂ F₂ (weak F₁ · $ this {refl}) p))
 sound-↔ Γ t .(F₁ ((^[ u ] G') · H)) G (reduce-l {.t} {u} {v} {F₁} {G'} {H} p) = inf-V (traverse-hypos (F₁ (sub H G') == G) (F₁ ((^[ u ] G') · H) == G) Γ (inf-III-samectx (λ x → (F₁ x == G)) G' H)) (sound-↔ Γ t (F₁ (sub H G')) G p)
 sound-↔ Γ t F .(F₂ ((^[ u ] G) · H)) (reduce-r {.t} {u} {v} {F₂} {G} {H} p) = inf-V (traverse-hypos (F == F₂ (sub H G)) (F == F₂ ((^[ u ] G) · H)) Γ (inf-III-samectx (λ x → (F == F₂ x)) G H)) (sound-↔ Γ t F (F₂ (sub H G)) p)

 sound-==-elim : ∀ {n Γ-t} → (Γ : FSC-Ctx n Γ-t) (F : Form Γ-t $o) (t : Type n) (G H : Form Γ-t t) →
  Γ , F ⊢ G == H →
  ⊢ (hypos Γ (F => (G == H)))
 sound-==-elim Γ .(G == H) t G H use = traverse-hypos-use ((G == H) => (G == H)) Γ (inf-V (inf-V ax-4-s ax-1-s) ax-2-s)
 sound-==-elim Γ F t G H (use' p) = traverse-hypos-use (F => (G == H)) Γ (hn-form (λ z → z => (G == H)) _ 2 (subst (λ z → ⊢ (z => (G == H))) p (hn-form (λ z → headNorm 2 (G == H) => z) _ 2 (inf-V (inf-V ax-4-s ax-1-s) ax-2-s))))
 sound-==-elim Γ .(H == G) t G H use-sym = traverse-hypos-use ((H == G) => (G == H)) Γ (lem15 H G)
 sound-==-elim Γ .(F & G') t G H (&-E-l {F} {G'} p) = inf-V (traverse-hypos (F => (G == H)) ((F & G') => (G == H)) Γ (lem6 F G' (G == H))) (sound-==-elim Γ F t G H p)
 sound-==-elim Γ .(F & G') t G H (&-E-r {F} {G'} p) = inf-V (traverse-hypos (G' => (G == H)) ((F & G') => (G == H)) Γ (lem6b F G' (G == H))) (sound-==-elim Γ G' t G H p)
 sound-==-elim Γ .(F => G') t G H (=>-E {F} {G'} p₁ p₂) = inf-V (inf-V (traverse-hypos2 F (G' => (G == H)) ((F => G') => (G == H)) Γ (lem7 F G' (G == H))) (sound Γ F p₁)) (sound-==-elim Γ G' t G H p₂)
 sound-==-elim Γ .(![ u ] F) t G H (!-E {u} {F} G' p) = inf-V (traverse-hypos (sub G' F => (G == H)) (![ u ] F => (G == H)) Γ (inf-V (lem9 (![ u ] F) (sub G' F) (G == H)) (ax-5-s F G'))) (sound-==-elim Γ (sub G' F) t G H p)
 sound-==-elim Γ .(!'[ u ] F) t G H (!'-E {u} {F} G' p) = inf-V (traverse-hypos ((F · G') => (G == H)) (!'[ u ] F => (G == H)) Γ (inf-V (lem9 (!'[ u ] F) (F · G') (G == H)) (ax-5-s3 F G'))) (sound-==-elim Γ (F · G') t G H p)
 sound-==-elim Γ .(?[ u ] F) t G H (?-E {u} {F} p) = inf-V (traverse-hypos (sub (ι u F) F => (G == H)) (?[ u ] F => (G == H)) Γ (inf-V (lem9 (?[ u ] F) (sub (ι u F) F) (G == H)) (ax-11-s {_} {_} {_} {F}))) (sound-==-elim Γ (sub (ι u F) F) t G H p)
 sound-==-elim Γ .(?'[ u ] F) t G H (?'-E {u} {F} p) = inf-V (traverse-hypos ((F · ι' u F) => (G == H)) (?'[ u ] F => (G == H)) Γ (inf-V (lem9 (?'[ u ] F) (F · ι' u F) (G == H)) (ax-11-s2 F))) (sound-==-elim Γ (F · ι' u F) t G H p)
 sound-==-elim Γ .(F ((^[ u ] G') · H')) t G H (reduce {u} {v} {F} {G'} {H'} p) = inf-V (traverse-hypos (F (sub H' G') => (G == H)) (F ((^[ u ] G') · H') => (G == H)) Γ (inf-V (lem9 (F ((^[ u ] G') · H')) (F (sub H' G')) (G == H)) (inf-II-samectx (λ x → (F x)) G' H'))) (sound-==-elim Γ (F (sub H' G')) t G H p)
 sound-==-elim Γ .(F == G) t H I (r-bool-ext {F} {G} p) = inf-V (traverse-hypos (((F => G) & (G => F)) => (H == I)) ((F == G) => (H == I)) Γ (inf-V (lem9 (F == G) ((F => G) & (G => F)) (H == I)) (inf-V (lem2 (F == G) (F => G) (G => F)) (inf-V (inf-V (lemb1 ((F == G) => (F => G)) ((F == G) => (G => F))) (inf-V ax-3-s (inf-V (inf-V ax-4-s (inf-V (lem5 (F == G) (G == F)) (lem15 F G))) (inf-V ax-3-s (lem13 F G))))) (lem13 G F))))) (sound-==-elim Γ ((F => G) & (G => F)) t H I p)
 sound-==-elim Γ .(F == G) t H I (r-fun-ext {u} {v} {F} {G} J p) = inf-V (traverse-hypos (((F · J) == (G · J)) => (H == I)) ((F == G) => (H == I)) Γ (inf-V (lem9 (F == G) ((F · J) == (G · J)) (H == I)) (inf-V (inf-V (lem4 (F == G) (J == J) ((F · J) == (G · J))) (lem16 F G J J)) (lem12 J)))) (sound-==-elim Γ ((F · J) == (G · J)) t H I p)


sound-top : {n : ℕ} (F : Form {n} ε $o) →
            ε ⊢ F →
            ⊢ F
sound-top = sound ε

