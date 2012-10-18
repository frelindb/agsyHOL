module HelpDefs where

-- open import Relation.Binary.PropositionalEquality

open import StdLibStuff

open import Syntax
open import FSC
open import STT
open import DerivedProps


m-weak-h : ∀ {n} Γ₁ Γ₂ {t} → {Γ₃ : Ctx n} → Form (Γ₃ ++ Γ₁) t → Form (Γ₃ ++ (Γ₂ r++ Γ₁)) t
m-weak-h {n} Γ₁ ε = λ f → f
m-weak-h {n} Γ₁ (t' ∷ Γ₂) {t} {Γ₃} = λ f → m-weak-h {n} (t' ∷ Γ₁) Γ₂ {t} {Γ₃} (weak-i Γ₃ Γ₁ f)

m-weak2 : ∀ {n Γ₁} Γ₂ → {t : Type n} → Form Γ₁ t → Form (Γ₂ ++ Γ₁) t
m-weak2 {n} {Γ₁} ε f = f
m-weak2 {n} {Γ₁} (t' ∷ Γ₂) f = weak (m-weak2 {n} {Γ₁} Γ₂ f)

hypos-i-h : ∀ {n Γ-t₁ Γ-t₂ Γ-t₃} → FSC-Ctx n Γ-t₁ → Form (Γ-t₃ ++ (Γ-t₂ r++ Γ-t₁)) $o → Form (Γ-t₃ ++ (Γ-t₂ r++ Γ-t₁)) $o
hypos-i-h ε = λ f → f
hypos-i-h {n} {Γ-t₁} {Γ-t₂} {Γ-t₃} (h ∷h Γ) = λ f → hypos-i-h {n} {Γ-t₁} {Γ-t₂} {Γ-t₃} Γ (m-weak-h Γ-t₁ Γ-t₂ {$o} {Γ-t₃} (m-weak2 Γ-t₃ h) => f)
hypos-i-h {n} {.(t ∷ _)} {Γ-t₂} {Γ-t₃} (t ∷ Γ) = hypos-i-h {n} {_} {t ∷ Γ-t₂} {Γ-t₃} Γ


m-weak : ∀ {n Γ₁ Γ₂ t} → Form Γ₁ t → Form (Γ₂ r++ Γ₁) t
m-weak {n} {Γ₁} {Γ₂} {t} = m-weak-h {n} Γ₁ Γ₂ {t} {ε}

hypos-i : ∀ {n Γ-t₁ Γ-t₂} → FSC-Ctx n Γ-t₁ → Form (Γ-t₂ r++ Γ-t₁) $o → Form (Γ-t₂ r++ Γ-t₁) $o
hypos-i {n} {Γ-t₁} {Γ-t₂} = hypos-i-h {n} {Γ-t₁} {Γ-t₂} {ε}

hypos : ∀ {n Γ-t} → FSC-Ctx n Γ-t → Form Γ-t $o → Form Γ-t $o
hypos {n} {Γ-t} = hypos-i {n} {Γ-t} {ε}


-- Props


eq-1-i : ∀ {n} Γ₁ Γ₂ → (t : Type n) (X₁ : Form (t ∷ Γ₁) $o) (X₂ : Form Γ₁ $o) →
         X₁ ≡ weak-i {n} {$o} {t} ε Γ₁ X₂ →
         m-weak-h Γ₁ Γ₂ {$o} {t ∷ ε} X₁ ≡ weak-i {n} {$o} {t} ε (Γ₂ r++ Γ₁) (m-weak-h Γ₁ Γ₂ {$o} {ε} X₂)
eq-1-i Γ₁ ε t X₁ X₂ = λ h → h
eq-1-i Γ₁ (u ∷ Γ₂) t X₁ X₂ = λ h → eq-1-i (u ∷ Γ₁) Γ₂ t (weak-i {_} {$o} {u} (t ∷ ε) Γ₁ X₁) (weak-i {_} {$o} {u} ε Γ₁ X₂) (trans (cong (weak-i {_} {$o} {u} (t ∷ ε) Γ₁) h) (weak-weak-p-1 Γ₁ t u $o X₂))

eq-1 : ∀ {n} Γ₁ Γ₂ → (t : Type n) (X : Form Γ₁ $o) →
       m-weak-h Γ₁ Γ₂ {$o} {t ∷ ε} (weak-i {n} {$o} {t} ε Γ₁ X) ≡ weak-i {n} {$o} {t} ε (Γ₂ r++ Γ₁) (m-weak-h Γ₁ Γ₂ {$o} {ε} X)
eq-1 Γ₁ Γ₂ t X = eq-1-i Γ₁ Γ₂ t (weak-i {_} {$o} {t} ε Γ₁ X) X refl


eq-2-2 : ∀ n → (Γ-t Γ' : Ctx n) → (t : Type n) (X₁ : Form (t ∷ Γ-t) $o) (X₂ : Form Γ-t $o) →
 weak-i {n} {$o} {t} ε Γ-t X₂ ≡ X₁ →
 (h₂ : t ∷ (Γ' r++ Γ-t) ≡ (Γ' ++ (t ∷ ε)) r++ Γ-t) →
 m-weak-h Γ-t (Γ' ++ (t ∷ ε)) {$o} {ε} X₂ ≡
 subst (λ z → Form z $o) h₂ (m-weak-h Γ-t Γ' {$o} {t ∷ ε} X₁)
eq-2-2 n Γ-t ε t X₁ X₂ h refl = h
eq-2-2 n Γ-t (u ∷ Γ') t X₁ X₂ h h₂ = eq-2-2 n (u ∷ Γ-t) Γ' t (weak-i {_} {$o} {u} (t ∷ ε) Γ-t X₁) (weak-i {_} {$o} {u} ε Γ-t X₂) (
 trans (sym (weak-weak-p-1 Γ-t t u $o X₂)) (cong (weak-i {_} {$o} {u} (t ∷ ε) Γ-t) h))
 h₂

eq-2-1 : ∀ n → (Γ-t Γ' : Ctx n) → (t : Type n) (h : Form Γ-t $o) (F : Form (t ∷ (Γ' r++ Γ-t)) $o) →
         (Γ'' : Ctx n)
         (h₁₁ : Γ'' ≡ (Γ' ++ (t ∷ ε)) r++ Γ-t) →
         (h₁₂ : t ∷ (Γ' r++ Γ-t) ≡  Γ'') →
         app (app A (app N (m-weak-h Γ-t (Γ' ++ (t ∷ ε)) {$o} {ε} h))) (subst (λ z → Form z $o) h₁₁ (subst (λ z → Form z $o) h₁₂ F)) ≡
         subst (λ z → Form z $o) h₁₁ (app (app A (app N (subst (λ z → Form z $o) h₁₂ (m-weak-h Γ-t Γ' {$o} {t ∷ ε} (weak-i ε Γ-t h))))) (subst (λ z → Form z $o) h₁₂ F))
eq-2-1 n Γ-t Γ' t h F .((Γ' ++ (t ∷ ε)) r++ Γ-t) refl h₁₂ = cong (λ z → app (app A (app N z)) (subst (λ z → Form z $o) h₁₂ F)) (eq-2-2 n Γ-t Γ' t (weak-i {_} {$o} {t} ε Γ-t h) h refl h₁₂)

eq-2-i : ∀ {n} Γ-t → (t : Type n) (Γ : FSC-Ctx n Γ-t) (Γ' : Ctx n) (F : Form (t ∷ (Γ' r++ Γ-t)) $o) →
       (h₁ : t ∷ (ε ++ (Γ' r++ Γ-t)) ≡ (Γ' ++ (t ∷ ε)) r++ Γ-t) →
       hypos-i-h {n} {Γ-t} {Γ' ++ (t ∷ ε)} {ε} Γ (subst (λ z → Form z $o) h₁ F) ≡ subst (λ z → Form z $o) h₁ (hypos-i-h {n} {Γ-t} {Γ'} {t ∷ ε} Γ F)
eq-2-i .ε t ε Γ' F h₁ = refl
eq-2-i .(u ∷ _) t (u ∷ Γ) Γ' F h₁ = eq-2-i _ t Γ (u ∷ Γ') F h₁
eq-2-i Γ-t t (h ∷h Γ) Γ' F h₁ = trans (cong (hypos-i-h {_} {Γ-t} {Γ' ++ (t ∷ ε)} {ε} Γ) (eq-2-1 _ Γ-t Γ' t h F _ h₁ refl)) (eq-2-i Γ-t t Γ Γ' (app (app A (app N (m-weak-h Γ-t Γ' {$o} {t ∷ ε} (weak-i ε Γ-t h)))) F) h₁)

eq-2 : ∀ {n Γ-t} → (t : Type n) (Γ : FSC-Ctx n Γ-t) (F : Form (t ∷ Γ-t) $o) →
       hypos-i-h {n} {Γ-t} {t ∷ ε} {ε} Γ F ≡ hypos-i-h {n} {Γ-t} {ε} {t ∷ ε} Γ F
eq-2 {_} {Γ-t} t Γ F = eq-2-i {_} Γ-t t Γ ε F refl



traverse-hypos-i : ∀ {n Γ-t₁ Γ-t₂} → (F G : Form (Γ-t₂ r++ Γ-t₁) $o) (Γ : FSC-Ctx n Γ-t₁) → (⊢ (F => G)) → ⊢ (hypos-i {n} {Γ-t₁} {Γ-t₂} Γ F => hypos-i {n} {Γ-t₁} {Γ-t₂} Γ G)
traverse-hypos-i F G ε h = h
traverse-hypos-i {n} {Γ-t₁} {Γ-t₂} F G (X ∷h Γ) h = traverse-hypos-i {n} {Γ-t₁} {Γ-t₂} (m-weak {n} {Γ-t₁} {Γ-t₂} X => F) (m-weak {n} {Γ-t₁} {Γ-t₂} X => G) Γ (inf-V ax-4-s h)
traverse-hypos-i {n} {.(t ∷ _)} {Γ-t₂} F G (t ∷ Γ) h = traverse-hypos-i {n} {_} {t ∷ Γ-t₂} F G Γ h

traverse-hypos : ∀ {n Γ-t} → (F G : Form Γ-t $o) (Γ : FSC-Ctx n Γ-t) → (⊢ (F => G)) → ⊢ (hypos Γ F => hypos Γ G)
traverse-hypos {n} {Γ-t} = traverse-hypos-i {n} {Γ-t} {ε}



traverse-hypos-pair-I-i : ∀ {n Γ-t₁ Γ-t₂} → (F G : Form (Γ-t₂ r++ Γ-t₁) $o) (Γ : FSC-Ctx n Γ-t₁) → ⊢ (hypos-i {n} {Γ-t₁} {Γ-t₂} Γ F => (hypos-i {n} {Γ-t₁} {Γ-t₂} Γ G => hypos-i {n} {Γ-t₁} {Γ-t₂} Γ (F & G)))
traverse-hypos-pair-I-i F G ε = lemb1 F G
traverse-hypos-pair-I-i {n} {Γ-t₁} {Γ-t₂} F G (x ∷h Γ) = inf-V (inf-V (ax-4-s {_} {_} {(hypos-i {n} {Γ-t₁} {Γ-t₂} Γ (m-weak {n} {Γ-t₁} {Γ-t₂} x => G) => (hypos-i {n} {Γ-t₁} {Γ-t₂} Γ ((m-weak {n} {Γ-t₁} {Γ-t₂} x => F) & (m-weak {n} {Γ-t₁} {Γ-t₂} x => G))))})
 (inf-V (ax-4-s {_} {_} {(hypos-i {n} {Γ-t₁} {Γ-t₂} Γ ((m-weak {n} {Γ-t₁} {Γ-t₂} x => F) & (m-weak {n} {Γ-t₁} {Γ-t₂} x => G)))}) (traverse-hypos-i {n} {Γ-t₁} {Γ-t₂} ((m-weak {n} {Γ-t₁} {Γ-t₂} x => F) & (m-weak {n} {Γ-t₁} {Γ-t₂} x => G)) (m-weak {n} {Γ-t₁} {Γ-t₂} x => (F & G)) Γ (lem2 (m-weak {n} {Γ-t₁} {Γ-t₂} x) F G))))
 (traverse-hypos-pair-I-i {n} {Γ-t₁} {Γ-t₂} (m-weak {n} {Γ-t₁} {Γ-t₂} x => F) (m-weak {n} {Γ-t₁} {Γ-t₂} x => G) Γ)
traverse-hypos-pair-I-i {n} {.(t ∷ _)} {Γ-t₂} F G (t ∷ Γ) = traverse-hypos-pair-I-i {n} {_} {t ∷ Γ-t₂} F G Γ

traverse-hypos-pair-I : ∀ {n Γ-t} → (F G : Form Γ-t $o) (Γ : FSC-Ctx n Γ-t) → ⊢ (hypos Γ F => (hypos Γ G => hypos Γ (F & G)))
traverse-hypos-pair-I {n} {Γ-t} = traverse-hypos-pair-I-i {n} {Γ-t} {ε}


traverse-hypos-elim-i : ∀ {n Γ-t₁ Γ-t₂} → (F : Form (Γ-t₂ r++ Γ-t₁) $o) (Γ : FSC-Ctx n Γ-t₁) (x : HVar Γ) → ⊢ (hypos-i {n} {Γ-t₁} {Γ-t₂} Γ (m-weak {n} {Γ-t₁} {Γ-t₂} (lookup-hyp Γ x) => F) => hypos-i {n} {Γ-t₁} {Γ-t₂} Γ F)
traverse-hypos-elim-i {n} {Γ-t₁} {Γ-t₂} F .(h ∷h Γ) (zero {._} {h} {Γ}) = traverse-hypos-i {n} {Γ-t₁} {Γ-t₂} (m-weak {n} {Γ-t₁} {Γ-t₂} h => (m-weak {n} {Γ-t₁} {Γ-t₂} h => F)) (m-weak {n} {Γ-t₁} {Γ-t₂} h => F) Γ (lem3 (m-weak {n} {Γ-t₁} {Γ-t₂} h) F)
traverse-hypos-elim-i {n} {Γ-t₁} {Γ-t₂} F .(h ∷h Γ) (succ {._} {h} {Γ} x) = inf-V ax-3-s (inf-V (inf-V (ax-4-s {_} {_} {~ (hypos-i {n} {Γ-t₁} {Γ-t₂} Γ (m-weak {n} {Γ-t₁} {Γ-t₂} (lookup-hyp Γ x) => (m-weak {n} {Γ-t₁} {Γ-t₂} h => F)))}) (inf-V (lem5 (hypos-i {n} {Γ-t₁} {Γ-t₂} Γ (m-weak {n} {Γ-t₁} {Γ-t₂} h => (m-weak {n} {Γ-t₁} {Γ-t₂} (lookup-hyp Γ x) => F))) (hypos-i {n} {Γ-t₁} {Γ-t₂} Γ (m-weak {n} {Γ-t₁} {Γ-t₂} (lookup-hyp Γ x) => (m-weak {n} {Γ-t₁} {Γ-t₂} h => F)))) (traverse-hypos-i {n} {Γ-t₁} {Γ-t₂} (m-weak {n} {Γ-t₁} {Γ-t₂} h => (m-weak {n} {Γ-t₁} {Γ-t₂} (lookup-hyp Γ x) => F)) (m-weak {n} {Γ-t₁} {Γ-t₂} (lookup-hyp Γ x) => (m-weak {n} {Γ-t₁} {Γ-t₂} h => F)) Γ (lem4 (m-weak {n} {Γ-t₁} {Γ-t₂} h) (m-weak {n} {Γ-t₁} {Γ-t₂} (lookup-hyp Γ x)) F)))) (inf-V ax-3-s (traverse-hypos-elim-i {n} {Γ-t₁} {Γ-t₂} (m-weak {n} {Γ-t₁} {Γ-t₂} h => F) Γ x)))
traverse-hypos-elim-i {n} {.(t ∷ _)} {Γ-t₂} F (t ∷ Γ) (skip x) = traverse-hypos-elim-i {n} {_} {t ∷ Γ-t₂} F Γ x

traverse-hypos-elim : ∀ {n Γ-t} → (F : Form Γ-t $o) (Γ : FSC-Ctx n Γ-t) (x : HVar Γ) → ⊢ (hypos Γ (lookup-hyp Γ x => F) => hypos Γ F)
traverse-hypos-elim {n} {Γ-t} = traverse-hypos-elim-i {n} {Γ-t} {ε}


traverse-hypos-use-i : ∀ {n Γ-t₁ Γ-t₂} → (F : Form (Γ-t₂ r++ Γ-t₁) $o) (Γ : FSC-Ctx n Γ-t₁) → ⊢ (F) → ⊢ (hypos-i {n} {Γ-t₁} {Γ-t₂} Γ F)
traverse-hypos-use-i F ε h = h
traverse-hypos-use-i {n} {Γ-t₁} {Γ-t₂} F (X ∷h Γ) h = traverse-hypos-use-i {n} {Γ-t₁} {Γ-t₂} (m-weak {n} {Γ-t₁} {Γ-t₂} X => F) Γ (inf-V ax-3-s (inf-V ax-2-s h))
traverse-hypos-use-i {n} {.(t ∷ _)} {Γ-t₂} F (t ∷ Γ) h = traverse-hypos-use-i {n} {_} {t ∷ Γ-t₂} F Γ h

traverse-hypos-use : ∀ {n Γ-t} → (F : Form Γ-t $o) (Γ : FSC-Ctx n Γ-t) → ⊢ (F) → ⊢ (hypos Γ F)
traverse-hypos-use {n} {Γ-t} = traverse-hypos-use-i {n} {Γ-t} {ε}


traverse-hypos2-i : ∀ {n Γ-t₁ Γ-t₂} → (F G H : Form (Γ-t₂ r++ Γ-t₁) $o) (Γ : FSC-Ctx n Γ-t₁) → (⊢ (F => (G => H))) → ⊢ (hypos-i {n} {Γ-t₁} {Γ-t₂} Γ F => (hypos-i {n} {Γ-t₁} {Γ-t₂}Γ G => hypos-i {n} {Γ-t₁} {Γ-t₂} Γ H))
traverse-hypos2-i F G H ε imp = imp
traverse-hypos2-i {n} {Γ-t₁} {Γ-t₂} F G H (X ∷h Γ) imp = traverse-hypos2-i {n} {Γ-t₁} {Γ-t₂} (m-weak {n} {Γ-t₁} {Γ-t₂} X => F) (m-weak {n} {Γ-t₁} {Γ-t₂} X => G) (m-weak {n} {Γ-t₁} {Γ-t₂} X => H) Γ (inf-V (lem8 (m-weak {n} {Γ-t₁} {Γ-t₂} X) F G H) imp)
traverse-hypos2-i {n} {.(t ∷ _)} {Γ-t₂} F G H (t ∷ Γ) imp = traverse-hypos2-i {n} {_} {t ∷ Γ-t₂} F G H Γ imp

traverse-hypos2 : ∀ {n Γ-t} → (F G H : Form Γ-t $o) (Γ : FSC-Ctx n Γ-t) → (⊢ (F => (G => H))) → ⊢ (hypos Γ F => (hypos Γ G => hypos Γ H))
traverse-hypos2 {n} {Γ-t} = traverse-hypos2-i {n} {Γ-t} {ε}

traverse-hypos3-i : ∀ {n Γ-t₁ Γ-t₂} → (F G H I : Form (Γ-t₂ r++ Γ-t₁) $o) (Γ : FSC-Ctx n Γ-t₁) → (⊢ (F => (G => (H => I)))) → ⊢ (hypos-i {n} {Γ-t₁} {Γ-t₂} Γ F => (hypos-i {n} {Γ-t₁} {Γ-t₂}Γ G => (hypos-i {n} {Γ-t₁} {Γ-t₂} Γ H => hypos-i {n} {Γ-t₁} {Γ-t₂} Γ I)))
traverse-hypos3-i F G H I ε imp = imp
traverse-hypos3-i {n} {Γ-t₁} {Γ-t₂} F G H I (X ∷h Γ) imp = traverse-hypos3-i {n} {Γ-t₁} {Γ-t₂} (m-weak {n} {Γ-t₁} {Γ-t₂} X => F) (m-weak {n} {Γ-t₁} {Γ-t₂} X => G) (m-weak {n} {Γ-t₁} {Γ-t₂} X => H) (m-weak {n} {Γ-t₁} {Γ-t₂} X => I) Γ (inf-V (lem8-3 (m-weak {n} {Γ-t₁} {Γ-t₂} X) F G H I) imp)
traverse-hypos3-i {n} {.(t ∷ _)} {Γ-t₂} F G H I (t ∷ Γ) imp = traverse-hypos3-i {n} {_} {t ∷ Γ-t₂} F G H I Γ imp

traverse-hypos3 : ∀ {n Γ-t} → (F G H I : Form Γ-t $o) (Γ : FSC-Ctx n Γ-t) → (⊢ (F => (G => (H => I)))) → ⊢ (hypos Γ F => (hypos Γ G => (hypos Γ H => hypos Γ I)))
traverse-hypos3 {n} {Γ-t} = traverse-hypos3-i {n} {Γ-t} {ε}


traverse-=>-I-dep-i : ∀ {n Γ-t₁ Γ-t₂} → (t : Type n) (F : Form (t ∷ (Γ-t₂ r++ Γ-t₁)) $o) (Γ : FSC-Ctx n Γ-t₁) → 
                      ⊢ (![ t ] hypos-i-h {n} {Γ-t₁} {Γ-t₂} {t ∷ ε} Γ F) →
                      ⊢ (hypos-i {n} {Γ-t₁} {Γ-t₂} Γ (![ t ] F))
traverse-=>-I-dep-i t F ε h = h
traverse-=>-I-dep-i {n} {Γ-t₁} {Γ-t₂} t F (X ∷h Γ) h = inf-V (traverse-hypos-i {n} {Γ-t₁} {Γ-t₂} (![ t ] (weak (m-weak {n} {Γ-t₁} {Γ-t₂} X) => F)) (m-weak {n} {Γ-t₁} {Γ-t₂} X => (![ t ] F)) Γ (ax-6-s {_} {_} {_} {~ (m-weak {n} {Γ-t₁} {Γ-t₂} X)} {F})) (traverse-=>-I-dep-i {n} {Γ-t₁} {Γ-t₂} t (weak (m-weak {n} {Γ-t₁} {Γ-t₂} X) => F) Γ
 (subst (λ z → ⊢_ {n} {_r++_ {n} Γ-t₂ Γ-t₁} (app {n} {_>_ {_} t ($o {_})} {$o {_}} {_r++_ {n} Γ-t₂ Γ-t₁} (Π {n} {t} {_r++_ {n} Γ-t₂ Γ-t₁}) (lam {n} {$o {_}} {_r++_ {n} Γ-t₂ Γ-t₁} t  ((hypos-i-h {n} {Γ-t₁} {Γ-t₂} {_∷_ {_} t (ε {_})} Γ (_=>_ {_} {_∷_ {_} t (_r++_ {n} Γ-t₂ Γ-t₁)} z F))))))
        (eq-1 {n} Γ-t₁ Γ-t₂ t X) h))
traverse-=>-I-dep-i {n} {.(t' ∷ _)} {Γ-t₂} t F (t' ∷ Γ) h = traverse-=>-I-dep-i {n} {_} {t' ∷ Γ-t₂} t F Γ h

traverse-=>-I-dep : ∀ {n Γ-t} → (t : Type n) (F : Form (t ∷ Γ-t) $o) (Γ : FSC-Ctx n Γ-t) → 
                    ⊢ (![ t ] hypos (t ∷ Γ) F) → ⊢ (hypos Γ (![ t ] F))
traverse-=>-I-dep {n} {Γ-t} t F Γ h = traverse-=>-I-dep-i {n} {Γ-t} {ε} t F Γ (subst (λ z → ⊢ app Π (lam t (z))) (eq-2 t Γ F) h)


traverse-=>-I-dep'-I2 : ∀ {n Γ-t₁ Γ-t₂} → (t : Type n) (F : Form (t ∷ (Γ-t₂ r++ Γ-t₁)) $o) (G : Form (Γ-t₂ r++ Γ-t₁) $o) (Γ : FSC-Ctx n Γ-t₁) → 
                        (⊢ (F => weak-i ε (Γ-t₂ r++ Γ-t₁) G)) →
                        ⊢ (hypos-i-h {n} {Γ-t₁} {Γ-t₂} {t ∷ ε} Γ F => weak-i ε (Γ-t₂ r++ Γ-t₁) (hypos-i-h {n} {Γ-t₁} {Γ-t₂} {ε} Γ G))
traverse-=>-I-dep'-I2 t F G ε h = h
traverse-=>-I-dep'-I2 {n} {t' ∷ Γ-t₁} {Γ-t₂} t F G (.t' ∷ Γ) h = traverse-=>-I-dep'-I2 {n} {Γ-t₁} {t' ∷ Γ-t₂} t F G Γ h
traverse-=>-I-dep'-I2 {n} {Γ-t₁} {Γ-t₂} t F G (X ∷h Γ) h = traverse-=>-I-dep'-I2 {n} {Γ-t₁} {Γ-t₂} t (m-weak-h Γ-t₁ Γ-t₂ {$o} {t ∷ ε} (weak-i ε Γ-t₁ X) => F) (m-weak-h Γ-t₁ Γ-t₂ {$o} {ε} X => G) Γ (
 subst (λ z → ⊢ ((m-weak-h Γ-t₁ Γ-t₂ {$o} {t ∷ ε} (weak-i ε Γ-t₁ X) => F) => (z => weak-i ε (Γ-t₂ r++ Γ-t₁) G))) (eq-1 Γ-t₁ Γ-t₂ t X) (inf-V ax-4-s h))

traverse-=>-I-dep'-I : ∀ {n Γ-t} → (t : Type n) (F : Form (t ∷ Γ-t) $o) (G : Form Γ-t $o) (Γ : FSC-Ctx n Γ-t) → 
                       (⊢ (F => weak-i ε Γ-t G)) →
                       ⊢ (hypos (t ∷ Γ) F => weak-i ε Γ-t (hypos Γ G))
traverse-=>-I-dep'-I {n} {Γ-t} t F G Γ h = subst (λ z → ⊢ (z => weak-i ε Γ-t (hypos Γ G))) (sym (eq-2 t Γ F)) (traverse-=>-I-dep'-I2 {n} {Γ-t} {ε} t F G Γ h)

traverse-=>-I-dep' : ∀ {n Γ-t} → (t : Type n) (F : Form Γ-t (t > $o)) (Γ : FSC-Ctx n Γ-t) → 
                     ⊢ hypos (t ∷ Γ) (weak F · $ this {refl}) → ⊢ (hypos Γ (!'[ t ] F))
traverse-=>-I-dep' t F Γ h = extend-context t (inf-V (traverse-=>-I-dep'-I t (weak F · $ this {refl}) (!'[ t ] F) Γ (inf-VI this (occurs-p-2 F) refl)) h)


-- -----------------------------------

traverse-hypos-eq-=>-I-i : ∀ {n Γ-t₁ Γ-t₂} → {t : Type n} → (F : Form (t ∷ (Γ-t₂ r++ Γ-t₁)) $o) (G : Form (Γ-t₂ r++ Γ-t₁) $o) (Γ : FSC-Ctx n Γ-t₁) → (⊢ (F => weak G)) → ⊢ hypos-i-h {n} {Γ-t₁} {Γ-t₂} {t ∷ ε} Γ F → ⊢ hypos-i {n} {Γ-t₁} {Γ-t₂} Γ G
traverse-hypos-eq-=>-I-i {n} {.ε} {Γ-t₂} {t} F G ε = λ z z' → extend-context t (inf-V z z')
traverse-hypos-eq-=>-I-i {n} {Γ-t₁} {Γ-t₂} {t} F G (X ∷h Γ) = λ h → traverse-hypos-eq-=>-I-i {n} {Γ-t₁} {Γ-t₂} {t} (m-weak-h {_} Γ-t₁ Γ-t₂ {_} {t ∷ ε} (m-weak2 (t ∷ ε) X) => F) (m-weak-h {_} Γ-t₁ Γ-t₂ {_} {ε} (m-weak2 ε X) => G) Γ (subst (λ z → ⊢ ((m-weak-h {_} Γ-t₁ Γ-t₂ {_} {t ∷ ε} (m-weak2 (t ∷ ε) X) => F) => (z => weak G))) (eq-1 Γ-t₁ Γ-t₂ t X) (inf-V ax-4-s h))
traverse-hypos-eq-=>-I-i {n} {t₁ ∷ Γ-t₁} {Γ-t₂} {t} F G ((.t₁) ∷ Γ) = traverse-hypos-eq-=>-I-i {n} {Γ-t₁} {t₁ ∷ Γ-t₂} {t} F G Γ

traverse-hypos-eq-=>-I'' : ∀ {n Γ-t} → {t : Type n} (F : Form (t ∷ Γ-t) $o) (G : Form Γ-t $o) (Γ : FSC-Ctx n Γ-t) →
 ⊢ (F => weak G) →
 ⊢ hypos (t ∷ Γ) F → ⊢ hypos Γ G
traverse-hypos-eq-=>-I'' {n} {Γ-t} F G Γ = λ h₁ h₂ → traverse-hypos-eq-=>-I-i {n} {Γ-t} {ε} F G Γ h₁ (subst (λ z → ⊢ z) (eq-2 _ Γ F) h₂)

tst3-ε : ∀ {n} → (Γ₁ Γ₂ : Ctx n) (F : Form Γ₁ $o)
 (eq : Γ₁ ≡ Γ₂) →
 ⊢_ {n} {Γ₂} (subst (λ z → Form z $o) eq F) →
 ⊢_ {n} {Γ₁} F
tst3-ε .Γ₂ Γ₂ F refl p = p  -- rewrite eq = p

tst3b : ∀ {n} → {t u : Type n} → (Γ-t₁ Γ-t₂ : Ctx n) (X : Form Γ-t₁ u) →
 (eq2 : t ∷ (Γ-t₂ r++ Γ-t₁) ≡ (Γ-t₂ ++ (t ∷ ε)) r++ Γ-t₁) →
 m-weak-h Γ-t₁ (Γ-t₂ ++ (t ∷ ε)) {_} {ε} X ≡
 subst (λ z → Form z u) eq2 (weak-i ε (Γ-t₂ r++ Γ-t₁) (m-weak-h Γ-t₁ Γ-t₂ {_} {ε} X))
tst3b Γ-t₁ ε X refl = refl
tst3b Γ-t₁ (v ∷ Γ-t₂) X eq2 = tst3b (v ∷ Γ-t₁) Γ-t₂ (weak-i ε Γ-t₁ X) eq2

tst3'-∷h : ∀ {n Γ-t₁ Γ-t₂} → {t : Type n} (F : Form (t ∷ (Γ-t₂ r++ Γ-t₁)) $o) (Γ : FSC-Ctx n Γ-t₁) →
 (X : Form Γ-t₁ $o)
 (Γ1 : Ctx n)
 (eq1 : Γ1 ≡ (Γ-t₂ ++ (t ∷ ε)) r++ Γ-t₁)
 (eq2 : t ∷ (Γ-t₂ r++ Γ-t₁) ≡ Γ1)
 (p : ⊢ hypos-i-h {n} {Γ-t₁} {Γ-t₂ ++ (t ∷ ε)} {ε} Γ (app (app A (app N (m-weak-h {n} Γ-t₁ (Γ-t₂ ++ (t ∷ ε)) {$o} {ε} X))) (subst (λ z → Form z $o) eq1 (subst (λ z → Form z $o) eq2 F)))) →
 ⊢ hypos-i-h {n} {Γ-t₁} {Γ-t₂ ++ (t ∷ ε)} {ε} Γ (subst (λ z → Form z $o) eq1 (app (app A (app N (subst (λ z → Form z $o) eq2 (weak-i ε (Γ-t₂ r++ Γ-t₁) (m-weak-h Γ-t₁ Γ-t₂ {$o} {ε} X))))) (subst (λ z → Form z $o) eq2 F)))
tst3'-∷h {n} {Γ-t₁} {Γ-t₂} {t} F Γ X .((Γ-t₂ ++ (t ∷ ε)) r++ Γ-t₁) refl eq2 p = subst (λ z → ⊢ hypos-i-h {n} {Γ-t₁} {Γ-t₂ ++ (t ∷ ε)} {ε} Γ (app (app A (app N z)) (subst (λ z → Form z $o) eq2 F))) (tst3b {n} {t} Γ-t₁ Γ-t₂ X eq2) p

tst3' : ∀ {n Γ-t₁ Γ-t₂} → {t : Type n} (F : Form (t ∷ (Γ-t₂ r++ Γ-t₁)) $o) (Γ : FSC-Ctx n Γ-t₁) →
 (eq : t ∷ (Γ-t₂ r++ Γ-t₁) ≡ (Γ-t₂ ++ (t ∷ ε)) r++ Γ-t₁) →
 ⊢ hypos-i-h {n} {Γ-t₁} {Γ-t₂ ++ (t ∷ ε)} {ε} Γ (subst (λ z → Form z $o) eq F) →
 ⊢ hypos-i-h {n} {Γ-t₁} {Γ-t₂} {ε} Γ (![ t ] F)
tst3' {n} {ε} {Γ-t₂} {t} F ε eq = λ p → inf-VI-s (tst3-ε {n} (t ∷ (Γ-t₂ r++ ε)) ((Γ-t₂ ++ (t ∷ ε)) r++ ε) F eq p)
tst3' {n} {t' ∷ Γ-t₁} {Γ-t₂} F ((.t') ∷ Γ) eq = tst3' {n} {Γ-t₁} {t' ∷ Γ-t₂} F Γ eq 
tst3' {n} {Γ-t₁} {Γ-t₂} {t} F (X ∷h Γ) eq = λ p → inf-V (traverse-hypos-i {n} {Γ-t₁} {Γ-t₂} (![ t ] (weak (~ (m-weak-h Γ-t₁ Γ-t₂ {_} {ε} X)) || F)) (m-weak-h {n} Γ-t₁ Γ-t₂ {$o} {ε} X => ![ t ] F) Γ (inf-V (inf-V ax-4-s ax-6-s) (lem2h2hb _))) (tst3' {n} {Γ-t₁} {Γ-t₂} {t} (weak (~ (m-weak-h Γ-t₁ Γ-t₂ {_} {ε} X)) || F) Γ eq (tst3'-∷h {n} {Γ-t₁} {Γ-t₂} {t} F Γ X (t ∷ (Γ-t₂ r++ Γ-t₁)) eq refl p))


traverse-hypos-eq-=>-I : ∀ {n Γ-t} → {t₁ t₂ : Type n} (F₁ F₂ : Form (t₁ ∷ Γ-t) t₂) (Γ : FSC-Ctx n Γ-t) →
 ⊢ hypos (t₁ ∷ Γ) (F₁ == F₂) →
 ⊢ hypos Γ (lam t₁ F₁ == lam t₁ F₂)
traverse-hypos-eq-=>-I {_} {Γ-t} {t₁} {t₂} F₁ F₂ Γ p = inf-V (traverse-hypos (![ t₁ ] (F₁ == F₂)) (lam t₁ F₁ == lam t₁ F₂) Γ ax-10-b-s) (tst3' {_} {Γ-t} {ε} (F₁ == F₂) Γ refl p)

