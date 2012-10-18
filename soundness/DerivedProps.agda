module DerivedProps where

{-
open import Relation.Binary.PropositionalEquality
open import Data.Nat hiding (_>_)
-}

open import StdLibStuff

open import Syntax
open import STT


lem3 : {n : ℕ} {Γ-t : Ctx n} (F G : Form Γ-t $o) → ⊢ ((F => (F => G)) => (F => G))
lem3 F G = inf-V (inf-V ax-4-s ax-1-s) (inf-V (inf-V ax-4-s (inf-V ax-4-s ax-2-s)) ax-3-s)

lem4 : {n : ℕ} {Γ-t : Ctx n} (F G H : Form Γ-t $o) →
       ⊢ ((F => (G => H)) => (G => (F => H)))
lem4 F G H = inf-V (inf-V ax-4-s ax-1-s) (inf-V (inf-V ax-4-s (inf-V ax-4-s (inf-V (inf-V ax-4-s (inf-V (inf-V ax-4-s ax-3-s) ax-2-s)) ax-2-s))) (inf-V (inf-V ax-4-s ax-3-s) (inf-V ax-4-s (inf-V ax-4-s (inf-V (inf-V ax-4-s ax-3-s) ax-2-s)))))

lem5 : {n : ℕ} {Γ-t : Ctx n} (F G : Form Γ-t $o) →
       ⊢ ((F => G) => (~ G => ~ F))
lem5 F G = inf-V (inf-V ax-4-s ax-3-s) (inf-V ax-4-s (inf-V ax-3-s (inf-V (inf-V ax-4-s ax-1-s) ax-2-s)))

lem6 : {n : ℕ} {Γ-t : Ctx n} (F G H : Form Γ-t $o) →
       ⊢ ((F => H) => ((F & G) => H))
lem6 F G H = inf-V (inf-V ax-4-s ax-3-s) (inf-V (inf-V ax-4-s (inf-V ax-4-s (inf-V (inf-V ax-4-s (inf-V ax-3-s (inf-V (inf-V ax-4-s ax-1-s) ax-2-s))) ax-2-s))) ax-3-s)

lem6b : {n : ℕ} {Γ-t : Ctx n} (F G H : Form Γ-t $o) →
       ⊢ ((G => H) => ((F & G) => H))
lem6b F G H = inf-V (inf-V ax-4-s ax-3-s) (inf-V (inf-V ax-4-s (inf-V ax-4-s (inf-V (inf-V ax-4-s (inf-V ax-3-s (inf-V (inf-V ax-4-s ax-1-s) ax-2-s))) (inf-V (inf-V ax-4-s ax-3-s) ax-2-s)))) ax-3-s)

lemb3 : {n : ℕ} {Γ-t : Ctx n} (F G : Form Γ-t $o) →
        ⊢ (F => ((F => G) => G))
lemb3 F G = inf-V ax-1-s (inf-V (inf-V ax-4-s ax-3-s) (inf-V (inf-V ax-4-s ax-2-s) (inf-V (inf-V ax-4-s ax-2-s) (inf-V ax-3-s (inf-V ax-4-s (inf-V (inf-V ax-4-s ax-3-s) ax-2-s))))))

lem7 : {n : ℕ} {Γ-t : Ctx n} (F G H : Form Γ-t $o) →
       ⊢ (F => ((G => H) => ((F => G) => H)))
lem7 F G H = inf-V (inf-V ax-4-s (lem4 (F => G) (G => H) H)) (inf-V (inf-V ax-4-s (inf-V ax-4-s (lemb3 G H))) (lemb3 F G))

lem8h : {n : ℕ} {Γ-t : Ctx n} (F G H : Form Γ-t $o) →
        ⊢ ((H => (F => G)) => ((H => F) => (H => G)))
lem8h F G H = inf-V (inf-V ax-4-s ax-1-s) (inf-V (inf-V ax-4-s (inf-V ax-4-s (inf-V (inf-V ax-4-s ax-3-s) (inf-V (inf-V ax-4-s ax-2-s) ax-2-s)))) (inf-V (inf-V ax-4-s ax-3-s) (inf-V ax-4-s ax-4-s)))

lem8 : {n : ℕ} {Γ-t : Ctx n} (X F G H : Form Γ-t $o) →
       ⊢ ((F => (G => H)) => ((X => F) => ((X => G) => (X => H))))
lem8 X F G H = inf-V (inf-V ax-4-s (inf-V ax-4-s (lem8h G H X))) (inf-V (inf-V ax-4-s (lem8h F (G => H) X)) (inf-V (lem4 X (F => (G => H)) (F => (G => H))) (inf-V ax-3-s (inf-V ax-2-s (inf-V (inf-V ax-4-s ax-1-s) ax-2-s)))))

lem8-3 : {n : ℕ} {Γ-t : Ctx n} (X F G H I : Form Γ-t $o) →
       ⊢ ((F => (G => (H => I))) => ((X => F) => ((X => G) => ((X => H) => (X => I)))))
lem8-3 X F G H I = inf-V (inf-V ax-4-s (inf-V ax-4-s (inf-V ax-4-s (lem8h H I X)))) (inf-V (inf-V ax-4-s (inf-V ax-4-s (lem8h G (H => I) X))) (inf-V (inf-V ax-4-s (lem8h F (G => (H => I)) X)) (inf-V (lem4 X (F => (G => (H => I))) (F => (G => (H => I)))) (inf-V ax-3-s (inf-V ax-2-s (inf-V (inf-V ax-4-s ax-1-s) ax-2-s))))))

lemb2 : {n : ℕ} {Γ-t : Ctx n} (F : Form Γ-t $o) →
        ⊢ (~ (~ F) => F)
lemb2 F = inf-V ax-3-s (inf-V (inf-V ax-4-s (inf-V ax-3-s (inf-V (inf-V ax-4-s ax-1-s) ax-2-s))) (inf-V ax-3-s (inf-V (inf-V ax-4-s ax-1-s) ax-2-s)))

lem2h2h : {n : ℕ} {Γ-t : Ctx n} (F : Form Γ-t $o) →
          ⊢ (F => ~ (~ F))
lem2h2h F = inf-V ax-3-s (inf-V (inf-V ax-4-s ax-1-s) ax-2-s)

lem2h2hb : {n : ℕ} {Γ-t : Ctx n} (F : Form Γ-t $o) →
           ⊢ (F => F)
lem2h2hb F = inf-V (inf-V ax-4-s ax-1-s) ax-2-s

lem2h2 : {n : ℕ} {Γ-t : Ctx n} (F G H : Form Γ-t $o) →
         ⊢ ((F || (G || H)) => ((F || G) || H))
lem2h2 F G H = inf-V (inf-V ax-4-s (inf-V ax-4-s (lemb2 H))) (inf-V (inf-V ax-4-s ax-3-s) (inf-V (inf-V ax-4-s (inf-V ax-4-s ax-3-s)) (inf-V (inf-V ax-4-s (inf-V ax-4-s (inf-V ax-4-s (lemb2 F)))) (inf-V (inf-V ax-4-s (inf-V ax-4-s ax-3-s)) (inf-V (inf-V ax-4-s (lem4 (~ F) (~ H) G)) (inf-V (inf-V ax-4-s ax-3-s) (inf-V (inf-V ax-4-s (inf-V ax-4-s (lem2h2h F))) (inf-V (inf-V ax-4-s ax-3-s) (inf-V (inf-V ax-4-s (inf-V ax-4-s ax-3-s)) (inf-V (inf-V ax-4-s (inf-V ax-4-s (inf-V ax-4-s (lem2h2h H)))) (lem2h2hb (F || (G || H)))))))))))))

lem2h1 : {n : ℕ} {Γ-t : Ctx n} (F G H : Form Γ-t $o) →
         ⊢ ((F => (G => H)) => ((F & G) => H))
lem2h1 F G H = inf-V (inf-V ax-4-s ax-3-s) (inf-V (inf-V ax-4-s (inf-V ax-4-s (inf-V ax-3-s (inf-V (inf-V ax-4-s ax-1-s) ax-2-s)))) (inf-V (inf-V ax-4-s ax-3-s) (inf-V (inf-V ax-4-s (lem2h2 (~ F) (~ G) H)) (inf-V (inf-V ax-4-s ax-1-s) ax-2-s))))

lemb1 : {n : ℕ} {Γ-t : Ctx n} (F G : Form Γ-t $o) →
        ⊢ (F => (G => (F & G)))
lemb1 F G = inf-V ax-1-s (inf-V (inf-V ax-4-s ax-3-s) (inf-V (inf-V ax-4-s ax-2-s) (inf-V (inf-V ax-4-s ax-3-s) (inf-V (inf-V ax-4-s ax-2-s) (inf-V ax-3-s (inf-V ax-4-s ax-2-s))))))


lem2 : {n : ℕ} {Γ-t : Ctx n} (F G H : Form Γ-t $o) → ⊢ (((F => G) & (F => H)) => (F => (G & H)))
lem2 F G H = inf-V (lem2h1 (F => G) (F => H) (F => (G & H))) (inf-V (lem8 F G H (G & H)) (lemb1 G H))


lem9 : {n : ℕ} {Γ-t : Ctx n} (F G H : Form Γ-t $o) →
       ⊢ ((F => G) => ((G => H) => (F => H)))
lem9 F G H = inf-V (inf-V ax-4-s (lem4 F (G => H) H)) (inf-V (inf-V ax-4-s (inf-V ax-4-s (lemb3 G H))) (inf-V (lem4 F (F => G) G) (lemb3 F G)))

lemb4 : {n : ℕ} {Γ-t : Ctx n} (F G : Form Γ-t $o) →
        ⊢ (F => (~ F => G))
lemb4 F G = inf-V (inf-V ax-4-s ax-2-s) (inf-V ax-3-s (inf-V (inf-V ax-4-s ax-1-s) ax-2-s))

lem5r : {n : ℕ} {Γ-t : Ctx n} (F G : Form Γ-t $o) →
       ⊢ ((~ F => ~ G) => (G => F))
lem5r F G = inf-V (inf-V ax-4-s (inf-V ax-4-s (lemb2 F))) (inf-V (inf-V ax-4-s ax-3-s) (lem2h2hb (~ F => ~ G)))

lemb5 : {n : ℕ} {Γ-t : Ctx n} (F G H : Form Γ-t $o) →
        ⊢ ((F => H) => ((G => H) => ((F || G) => H)))
lemb5 F G H = inf-V (inf-V ax-4-s (inf-V ax-4-s (lem5r H (F || G)))) (inf-V (inf-V ax-4-s ax-3-s) (inf-V (inf-V ax-4-s (inf-V ax-4-s (inf-V (lem5 (G => H) (~ H => ~ G)) (lem5 G H)))) (inf-V (inf-V ax-4-s ax-3-s) (inf-V ax-3-s (inf-V (inf-V ax-4-s (inf-V (lem5 (F => H) (~ H => ~ F)) (lem5 F H))) (inf-V ax-3-s (inf-V (lem8 (~ H) (~ F) (~ G) (~ (F || G))) (inf-V (inf-V ax-4-s (inf-V ax-4-s (inf-V (lem5 (F || G) (~ (~ F) || ~ (~ G))) (inf-V (inf-V ax-4-s (inf-V ax-4-s (lem2h2h G))) (inf-V (inf-V ax-4-s ax-3-s) (inf-V (inf-V ax-4-s (inf-V ax-4-s (lem2h2h F))) (inf-V (inf-V ax-4-s ax-3-s) (lem2h2hb (F || G))))))))) (lemb1 (~ F) (~ G))))))))))


-- ---------------

lem10 : {n : ℕ} {Γ-t : Ctx n} (F : Form Γ-t $o) →
        ⊢ ((F => $false) => ~ F)
lem10 F = inf-V ax-3-s (inf-V (inf-V ax-4-s (inf-V (lem5 (F => $false) (F => ~ F)) (inf-V ax-4-s (inf-V (inf-V ax-4-s (ax-5-s ($ this {refl}) (~ F))) (lem2h2hb (![ _ ] ($ this {refl}))))))) (inf-V ax-3-s ax-1-s))

lem11 : {n : ℕ} {Γ-t : Ctx n} (F : Form Γ-t $o) →
        ⊢ ($false => F)
lem11 F = inf-V (inf-V ax-4-s (ax-5-s ($ this {refl}) F)) (lem2h2hb (![ _ ] ($ this {refl})))


lem12 : {n : ℕ} {Γ-t : Ctx n} {t : Type n} (F : Form Γ-t t) →
        ⊢ (F == F)
lem12 {n} {Γ-t} {t} F = inf-V (inf-III-samectx {n} {Γ-t} {t} {t > $o} (λ z → (z · F)) (^[ t ] (![ t > $o ] (($ this {refl} · $ (next (next this)) {refl}) => ($ this {refl} · $ (next this) {refl})))) F) (inf-V (inf-III-samectx {n} {Γ-t} {t} {$o} (λ z → (z)) (![ t > $o ] (($ this {refl} · weak (weak F)) => ($ this {refl} · $ (next this) {refl}))) F) (inf-VI-s (subst (λ z → ⊢ ((($ this {refl} · z) => ($ this {refl} · weak F)))) (sub-weak-p-1 F F) (inf-V (inf-V ax-4-s ax-1-s) ax-2-s))))


lem13 : {n : ℕ} {Γ-t : Ctx n} (F G : Form Γ-t $o) →
        ⊢ ((G == F) => (F => G))
lem13 F G =
 inf-V (inf-III-samectx (λ z → ((z · F) => (F => G))) (^[ $o ] (![ $o > $o ] (($ this {refl} · $ (next (next this)) {refl}) => ($ this {refl} · $ (next this) {refl})))) G) (
 inf-V (inf-III-samectx (λ z → (z => (F => G))) (![ $o > $o ] (($ this {refl} · weak (weak G)) => ($ this {refl} · $ (next this) {refl}))) F) (
 subst (λ z → ⊢ ((![ $o > $o ] (($ this {refl} · z) => ($ this {refl} · weak F))) => (F => G))) (sub-weak-p-1 G F) (
 inf-V ax-3-s (
 inf-V (inf-V ax-4-s (inf-V (lem5 (![ $o > $o ] (($ this {refl} · weak G) => ($ this {refl} · weak F))) (((^[ $o ] ~ ($ this {refl})) · sub (^[ $o ] ~ ($ this {refl})) (weak G)) => ((^[ $o ] ~ ($ this {refl})) · sub (^[ $o ] ~ ($ this {refl})) (weak F))))
  (ax-5-s (($ this {refl} · weak G) => ($ this {refl} · weak F)) (^[ $o ] ~ ($ this {refl}))))) (
 inf-V ax-3-s (
 subst (λ z → ⊢ ((((^[ $o ] ~ ($ this {refl})) · z) => ((^[ $o ] ~ ($ this {refl})) · sub (^[ $o ] ~ ($ this {refl})) (weak F))) => (F => G))) (sub-weak-p-1' G (^[ $o ] ~ ($ this {refl}))) (
 subst (λ z → ⊢ ((((^[ $o ] ~ ($ this {refl})) · G) => ((^[ $o ] ~ ($ this {refl})) · z)) => (F => G))) (sub-weak-p-1' F (^[ $o ] ~ ($ this {refl}))) (
 inf-V (inf-III-samectx (λ z → ((z => ((^[ $o ] ~ ($ this {refl})) · F)) => (F => G))) (~ ($ this {refl})) G) (
 inf-V (inf-III-samectx (λ z → (((~ G) => z) => (F => G))) (~ ($ this {refl})) F) (
 lem5r G F
 ))))))))))
 
transitivity : {n : ℕ} {Γ-t : Ctx n} {t : Type n} (F G H : Form Γ-t t) →
         ⊢ ((F == G) => ((G == H) => (F == H)))
transitivity F G H = 
 inf-V (inf-III-samectx (λ z → ((z · G) => ((G == H) => (F == H)))) (^[ _ ] (![ _ > $o ] (($ this {refl} · $ (next (next this)) {refl}) => ($ this {refl} · $ (next this) {refl})))) F) (
 inf-V (inf-III-samectx (λ z → (z => ((G == H) => (F == H)))) (![ _ > $o ] (($ this {refl} · weak (weak F)) => ($ this {refl} · $ (next this) {refl}))) G) (
 subst (λ z → ⊢ ((![ _ > $o ] (($ this {refl} · z) => ($ this {refl} · weak G))) => ((G == H) => (F == H)))) (sub-weak-p-1 F G) (
 inf-V (inf-III-samectx (λ z → ((![ _ > $o ] (($ this {refl} · weak F) => ($ this {refl} · weak G))) => ((z · H) => (F == H)))) (^[ _ ] (![ _ > $o ] (($ this {refl} · $ (next (next this)) {refl}) => ($ this {refl} · $ (next this) {refl})))) G) (
 inf-V (inf-III-samectx (λ z → ((![ _ > $o ] (($ this {refl} · weak F) => ($ this {refl} · weak G))) => (z => (F == H)))) (![ _ > $o ] (($ this {refl} · weak (weak G)) => ($ this {refl} · $ (next this) {refl}))) H) (
 subst (λ z → ⊢ ((![ _ > $o ] (($ this {refl} · weak F) => ($ this {refl} · weak G))) => ((![ _ > $o ] (($ this {refl} · z) => ($ this {refl} · weak H))) => (F == H)))) (sub-weak-p-1 G H) (
 inf-V (inf-III-samectx (λ z → ((![ _ > $o ] (($ this {refl} · weak F) => ($ this {refl} · weak G))) => ((![ _ > $o ] (($ this {refl} · weak G) => ($ this {refl} · weak H))) => (z · H)))) (^[ _ ] (![ _ > $o ] (($ this {refl} · $ (next (next this)) {refl}) => ($ this {refl} · $ (next this) {refl})))) F) (
 inf-V (inf-III-samectx (λ z → ((![ _ > $o ] (($ this {refl} · weak F) => ($ this {refl} · weak G))) => ((![ _ > $o ] (($ this {refl} · weak G) => ($ this {refl} · weak H))) => z))) (![ _ > $o ] (($ this {refl} · weak (weak F)) => ($ this {refl} · $ (next this) {refl}))) H) (
 subst (λ z → ⊢ ((![ _ > $o ] (($ this {refl} · weak F) => ($ this {refl} · weak G))) => ((![ _ > $o ] (($ this {refl} · weak G) => ($ this {refl} · weak H))) => (![ _ > $o ] (($ this {refl} · z) => ($ this {refl} · weak H)))))) (sub-weak-p-1 F H) (
 inf-V (inf-V ax-4-s (ax-6-s {_} {_} {_} {~ (![ _ ] (($ this {refl} · weak G) => ($ this {refl} · weak H)))} {($ this {refl} · weak F) => ($ this {refl} · weak H)})) (
 inf-V (ax-6-s {_} {_} {_} {~ (![ _ ] (($ this {refl} · weak F) => ($ this {refl} · weak G)))} {(weak (![ _ ] (($ this {refl} · weak G) => ($ this {refl} · weak H)))) => (($ this {refl} · weak F) => ($ this {refl} · weak H))}) (
 inf-VI-s (
 inf-V ax-3-s (
 inf-V (inf-V ax-4-s (inf-V (lem5 (![ _ ] (($ this {refl} · weak-i (_ ∷ ε) _ (weak F)) => ($ this {refl} · weak-i (_ ∷ ε) _ (weak G)))) (sub ($ this {refl}) (($ this {refl} · weak-i (_ ∷ ε) _ (weak F)) => ($ this {refl} · weak-i (_ ∷ ε) _ (weak G)))))
  (ax-5-s (($ this {refl} · weak-i (_ ∷ ε) _ (weak F)) => ($ this {refl} · weak-i (_ ∷ ε) _ (weak G))) ($ this {refl})))) (
 inf-V ax-3-s (
 inf-V (inf-V ax-4-s ax-3-s) (
 inf-V (inf-V ax-4-s (inf-V ax-4-s (inf-V (lem5 (![ _ ] (($ this {refl} · weak-i (_ ∷ ε) _ (weak G)) => ($ this {refl} · weak-i (_ ∷ ε) _ (weak H)))) (sub ($ this {refl}) (($ this {refl} · weak-i (_ ∷ ε) _ (weak G)) => ($ this {refl} · weak-i (_ ∷ ε) _ (weak H)))))
  (ax-5-s (($ this {refl} · weak-i (_ ∷ ε) _ (weak G)) => ($ this {refl} · weak-i (_ ∷ ε) _ (weak H))) ($ this {refl}))))) (
 inf-V (inf-V ax-4-s ax-3-s) (
 subst (λ z → ⊢ (((($ this {refl}) · z) => (($ this {refl}) · (sub ($ this {refl}) (weak-i (_ ∷ ε) _ (weak G))))) => (((($ this {refl}) · (sub ($ this {refl}) (weak-i (_ ∷ ε) _ (weak G)))) => (($ this {refl}) · (sub ($ this {refl}) (weak-i (_ ∷ ε) _ (weak H))))) => (($ this {refl} · weak F) => ($ this {refl} · weak H))))) (sub-weak-p-23 F ($ this {refl})) (
 subst (λ z → ⊢ (((($ this {refl}) · (weak F)) => (($ this {refl}) · z)) => (((($ this {refl}) · (sub ($ this {refl}) (weak-i (_ ∷ ε) _ (weak G)))) => (($ this {refl}) · (sub ($ this {refl}) (weak-i (_ ∷ ε) _ (weak H))))) => (($ this {refl} · weak F) => ($ this {refl} · weak H))))) (sub-weak-p-23 G ($ this {refl})) (
 subst (λ z → ⊢ (((($ this {refl}) · (weak F)) => (($ this {refl}) · (weak G))) => (((($ this {refl}) · z) => (($ this {refl}) · (sub ($ this {refl}) (weak-i (_ ∷ ε) _ (weak H))))) => (($ this {refl} · weak F) => ($ this {refl} · weak H))))) (sub-weak-p-23 G ($ this {refl})) (
 subst (λ z → ⊢ (((($ this {refl}) · (weak F)) => (($ this {refl}) · (weak G))) => (((($ this {refl}) · (weak G)) => (($ this {refl}) · z)) => (($ this {refl} · weak F) => ($ this {refl} · weak H))))) (sub-weak-p-23 H ($ this {refl})) (
 lem9 ($ this {refl} · weak F) ($ this {refl} · weak G) ($ this {refl} · weak H)
 ))))))))))))))))))))))

lem14 : {n : ℕ} {Γ-t : Ctx n} {t : Type n} (F G H I : Form Γ-t t) →
        ⊢ ((F == G) => ((G == H) => ((H == I) => (F == I))))
lem14 F G H I = inf-V (inf-V ax-4-s (inf-V ax-4-s (transitivity F H I))) (transitivity F G H)

lem15 : {n : ℕ} {Γ-t : Ctx n} {t : Type n} (F G : Form Γ-t t) →
        ⊢ ((F == G) => (G == F))
lem15 F G = 
 inf-V (inf-III-samectx (λ z → ((z · G) => (G == F))) (^[ _ ] (![ _ > $o ] (($ this {refl} · $ (next (next this)) {refl}) => ($ this {refl} · $ (next this) {refl})))) F) (
 inf-V (inf-III-samectx (λ z → (z => (G == F))) (![ _ > $o ] (($ this {refl} · weak (weak F)) => ($ this {refl} · $ (next this) {refl}))) G) (
 subst (λ z → ⊢ ((![ _ > $o ] (($ this {refl} · z) => ($ this {refl} · weak G))) => (G == F))) (sub-weak-p-1 F G) (
 inf-V (inf-III-samectx (λ z → ((![ _ > $o ] (($ this {refl} · weak F) => ($ this {refl} · weak G))) => (z · F))) (^[ _ ] (![ _ > $o ] (($ this {refl} · $ (next (next this)) {refl}) => ($ this {refl} · $ (next this) {refl})))) G) (
 inf-V (inf-III-samectx (λ z → ((![ _ > $o ] (($ this {refl} · weak F) => ($ this {refl} · weak G))) => z)) (![ _ > $o ] (($ this {refl} · weak (weak G)) => ($ this {refl} · $ (next this) {refl}))) F) (
 subst (λ z → ⊢ ((![ _ > $o ] (($ this {refl} · weak F) => ($ this {refl} · weak G))) => (![ _ > $o ] (($ this {refl} · z) => ($ this {refl} · weak F))))) (sub-weak-p-1 G F) (
 inf-V (ax-6-s {_} {_} {_} {~ (![ _ ] (($ this {refl} · weak F) => ($ this {refl} · weak G)))} {($ this {refl} · weak G) => ($ this {refl} · weak F)}) (
 inf-VI-s (
 inf-V ax-3-s (
 inf-V (inf-V ax-4-s (inf-V (lem5 (![ _ ] (($ this {refl} · weak-i (_ ∷ ε) _ (weak F)) => ($ this {refl} · weak-i (_ ∷ ε) _ (weak G)))) (sub (^[ _ ] ~ ($ (next this) {refl} · $ this {refl})) (($ this {refl} · weak-i (_ ∷ ε) _ (weak F)) => ($ this {refl} · weak-i (_ ∷ ε) _ (weak G)))))
  (ax-5-s (($ this {refl} · weak-i (_ ∷ ε) _ (weak F)) => ($ this {refl} · weak-i (_ ∷ ε) _ (weak G))) (^[ _ ] ~ ($ (next this) {refl} · $ this {refl}))))) (
 inf-V ax-3-s (
 subst (λ z → ⊢ ((((^[ _ ] ~ ($ (next this) {refl} · $ this {refl})) · z) => ((^[ _ ] ~ ($ (next this) {refl} · $ this {refl})) · (sub (^[ _ ] ~ ($ (next this) {refl} · $ this {refl})) (weak-i (_ ∷ ε) _ (weak G))))) => (($ this {refl} · weak G) => ($ this {refl} · weak F)))) (sub-weak-p-23 F (^[ _ ] ~ ($ (next this) {refl} · $ this {refl}))) (
 subst (λ z → ⊢ ((((^[ _ ] ~ ($ (next this) {refl} · $ this {refl})) · (weak F)) => ((^[ _ ] ~ ($ (next this) {refl} · $ this {refl})) · z)) => (($ this {refl} · weak G) => ($ this {refl} · weak F)))) (sub-weak-p-23 G (^[ _ ] ~ ($ (next this) {refl} · $ this {refl}))) (
 inf-V (inf-III-samectx (λ z → ((z => ((^[ _ ] ~ ($ (next this) {refl} · $ this {refl})) · weak G)) => (($ this {refl} · weak G) => ($ this {refl} · weak F)))) (~ ($ (next this) {refl} · $ this {refl})) (weak F)) (
 inf-V (inf-III-samectx (λ z → (((~ ($ this {refl} · weak F)) => z) => (($ this {refl} · weak G) => ($ this {refl} · weak F)))) (~ ($ (next this) {refl} · $ this {refl})) (weak G)) (
 lem5r ($ this {refl} · weak F) ($ this {refl} · weak G)
 )))))))))))))))

substitutivity : {n : ℕ} {Γ-t : Ctx n} {t u : Type n} (F G : Form Γ-t t) (H : Form Γ-t (t > u)) →
        ⊢ ((F == G) => ((H · F) == (H · G)))
substitutivity F G H = 
 inf-V (inf-III-samectx (λ z → ((z · G) => ((H · F) == (H · G)))) (^[ _ ] (![ _ > _ ] (($ this {refl} · $ (next (next this)) {refl}) => ($ this {refl} · $ (next this) {refl})))) F) (
 inf-V (inf-III-samectx (λ z → (z => ((H · F) == (H · G)))) (![ _ > _ ] (($ this {refl} · weak (weak F)) => ($ this {refl} · $ (next this) {refl}))) G) (
 subst (λ z → ⊢ ((![ _ > _ ] (($ this {refl} · z) => ($ this {refl} · weak G))) => ((H · F) == (H · G)))) (sub-weak-p-1 F G) (
 inf-V (inf-III-samectx (λ z → ((![ _ > _ ] (($ this {refl} · weak F) => ($ this {refl} · weak G))) => (z · (H · G)))) (^[ _ ] (![ _ > _ ] (($ this {refl} · $ (next (next this)) {refl}) => ($ this {refl} · $ (next this) {refl})))) ((H · F))) (
 inf-V (inf-III-samectx (λ z → ((![ _ > _ ] (($ this {refl} · weak F) => ($ this {refl} · weak G))) => z)) (![ _ > _ ] (($ this {refl} · weak (weak ((H · F)))) => ($ this {refl} · $ (next this) {refl}))) ((H · G))) (
 subst (λ z → ⊢ ((![ _ > _ ] (($ this {refl} · weak F) => ($ this {refl} · weak G))) => (![ _ > _ ] (($ this {refl} · z) => ($ this {refl} · weak ((H · G))))))) (sub-weak-p-1 ((H · F)) ((H · G))) (
 inf-V (ax-6-s {_} {_} {_} {~ (![ _ ] (($ this {refl} · weak F) => ($ this {refl} · weak G)))} {($ this {refl} · weak ((H · F))) => ($ this {refl} · weak ((H · G)))}) (
 inf-VI-s (
 inf-V ax-3-s (
 inf-V (inf-V ax-4-s (inf-V (lem5 (![ _ ] (($ this {refl} · weak-i (_ ∷ ε) _ (weak F)) => ($ this {refl} · weak-i (_ ∷ ε) _ (weak G)))) (sub (^[ _ ] ($ (next this) {refl} · (weak (weak H) · $ this {refl}))) (($ this {refl} · weak-i (_ ∷ ε) _ (weak F)) => ($ this {refl} · weak-i (_ ∷ ε) _ (weak G)))))
  (ax-5-s (($ this {refl} · weak-i (_ ∷ ε) _ (weak F)) => ($ this {refl} · weak-i (_ ∷ ε) _ (weak G))) (^[ _ ] ($ (next this) {refl} · (weak (weak H) · $ this {refl})))))) (
 inf-V ax-3-s (
 subst (λ z → ⊢ ((((^[ _ ] ($ (next this) {refl} · (weak (weak H) · $ this {refl}))) · z) => ((^[ _ ] ($ (next this) {refl} · (weak (weak H) · $ this {refl}))) · (sub (^[ _ ] ($ (next this) {refl} · (weak (weak H) · $ this {refl}))) (weak-i (_ ∷ ε) _ (weak G))))) => (($ this {refl} · weak (H · F)) => ($ this {refl} · weak (H · G))))) {-{weak F} {sub (^[ _ ] ($ (next this) {refl} · (weak (weak H) · $ this {refl}))) (weak-i (_ ∷ ε) _ (weak F))}-} (sub-weak-p-23 F (^[ _ ] ($ (next this) {refl} · (weak (weak H) · $ this {refl})))) (
  subst (λ z → ⊢ ((((^[ _ ] ($ (next this) {refl} · (weak (weak H) · $ this {refl}))) · (weak F)) => ((^[ _ ] ($ (next this) {refl} · (weak (weak H) · $ this {refl}))) · z)) => (($ this {refl} · weak (H · F)) => ($ this {refl} · weak (H · G))))) {-{weak G} {sub (^[ _ ] ($ (next this) {refl} · (weak (weak H) · $ this {refl}))) (weak-i (_ ∷ ε) _ (weak G))}-} (sub-weak-p-23 G (^[ _ ] ($ (next this) {refl} · (weak (weak H) · $ this {refl})))) (
 inf-V (inf-III-samectx (λ z → ((z => ((^[ _ ] ($ (next this) {refl} · (weak (weak H) · $ this {refl}))) · weak G)) => (($ this {refl} · weak (H · F)) => ($ this {refl} · weak (H · G))))) ($ (next this) {refl} · (weak (weak H) · $ this {refl})) (weak F)) (
 subst (λ z → ⊢ ((($ this {refl} · (z · weak F)) => ((^[ _ ] ($ (next this) {refl} · (weak (weak H) · $ this {refl}))) · weak G)) => (($ this {refl} · weak (H · F)) => ($ this {refl} · weak (H · G))))) {-{weak H} {sub (weak F) (weak (weak H))}-} (sub-weak-p-1' (weak H) (weak F)) (
 inf-V (inf-III-samectx (λ z → ((($ this {refl} · weak (H · F)) => z) => (($ this {refl} · weak (H · F)) => ($ this {refl} · weak (H · G))))) ($ (next this) {refl} · (weak (weak H) · $ this {refl})) (weak G)) (
 subst (λ z → ⊢ ((($ this {refl} · (weak (H · F))) => ($ this {refl} · (z · weak G))) => (($ this {refl} · weak (H · F)) => ($ this {refl} · weak (H · G))))) {-{weak H} {sub (weak G) (weak (weak H))}-} (sub-weak-p-1' (weak H) (weak G)) (
 lem2h2hb (($ this {refl} · weak (H · F)) => ($ this {refl} · (weak H · weak G)))
 )))))))))))))))))


lem16 : {n : ℕ} {Γ-t : Ctx n} {α β : Type n} (F₁ F₂ : Form Γ-t (α > β)) (G₁ G₂ : Form Γ-t α) →
        ⊢ ((F₁ == F₂) => ((G₁ == G₂) => ((F₁ · G₁) == (F₂ · G₂))))
lem16 F₁ F₂ G₁ G₂ =
 inf-V (inf-V (inf-V (lem8 (F₁ == F₂) ((G₁ == G₂) => ((F₁ · G₁) == (F₂ · G₁))) ((G₁ == G₂) => ((F₂ · G₁) == (F₂ · G₂))) ((G₁ == G₂) => ((F₁ · G₁) == (F₂ · G₂))))
 (inf-V (lem8 (G₁ == G₂) ((F₁ · G₁) == (F₂ · G₁)) ((F₂ · G₁) == (F₂ · G₂)) ((F₁ · G₁) == (F₂ · G₂))) (
  transitivity (F₁ · G₁) (F₂ · G₁) (F₂ · G₂))))
 (inf-V (lem4 (G₁ == G₂) (F₁ == F₂) ((F₁ · G₁) == (F₂ · G₁))) (inf-V ax-3-s (inf-V ax-2-s (
  subst (λ z → ⊢ ((F₁ == F₂) => ((F₁ · G₁) == (F₂ · z)))) (sym (sub-weak-p-1' G₁ F₂)) (
  inf-V (inf-II-samectx (λ z → ((F₁ == F₂) => ((F₁ · G₁) == z))) (($ this {refl}) · weak G₁) F₂) (
  subst (λ z → ⊢ ((F₁ == F₂) => ((F₁ · z) == ((^[ _ ] (($ this {refl}) · weak G₁)) · F₂)))) (sym (sub-weak-p-1' G₁ F₁)) (
  inf-V (inf-II-samectx (λ z → ((F₁ == F₂) => (z == ((^[ _ ] (($ this {refl}) · weak G₁)) · F₂)))) (($ this {refl}) · weak G₁) F₁) (
  substitutivity F₁ F₂ (^[ _ ] (($ this {refl}) · weak G₁))
 )))))))))
 (inf-V ax-3-s (inf-V ax-2-s (
  subst (λ z → ⊢ ((G₁ == G₂) => ((F₂ · G₁) == (z · G₂)))) (sym (sub-weak-p-1' F₂ G₂)) (
  inf-V (inf-II-samectx (λ z → ((G₁ == G₂) => ((F₂ · G₁) == z))) (weak F₂ · ($ this {refl})) G₂) (
  subst (λ z → ⊢ ((G₁ == G₂) => ((z · G₁) == ((^[ _ ] (weak F₂ · ($ this {refl}))) · G₂)))) (sym (sub-weak-p-1' F₂ G₁)) (
  inf-V (inf-II-samectx (λ z → ((G₁ == G₂) => (z == ((^[ _ ] (weak F₂ · ($ this {refl}))) · G₂)))) (weak F₂ · ($ this {refl})) G₁) (
  substitutivity G₁ G₂ (^[ _ ] (weak F₂ · ($ this {refl})))
 )))))))
