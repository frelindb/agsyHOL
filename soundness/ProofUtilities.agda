module ProofUtilities where

-- open import Data.Nat hiding (_>_)

open import StdLibStuff

open import Syntax
open import FSC


mutual
 hn-left-i : {n : ℕ} {Γ-t : Ctx n} {Γ : FSC-Ctx n Γ-t} {α β : Type n} (m : ℕ) (S : Form Γ-t β → Form Γ-t α) (F : Form Γ-t β) (G : Form Γ-t α) → Γ ⊢ α ∋ S (headNorm m F) ↔ G → Γ ⊢ α ∋ S F ↔ G
 hn-left-i m S (app F H) G p = hn-left-i m (λ x → S (app x H)) F G (hn-left-i' m S (headNorm m F) H G p)
 hn-left-i _ _ (var _ _) _ p = p
 hn-left-i _ _ N _ p = p
 hn-left-i _ _ A _ p = p
 hn-left-i _ _ Π _ p = p
 hn-left-i _ _ i _ p = p
 hn-left-i _ _ (lam _ _) _ p = p

 hn-left-i' : {n : ℕ} {Γ-t : Ctx n} {Γ : FSC-Ctx n Γ-t} {α β γ : Type n} (m : ℕ) (S : Form Γ-t β → Form Γ-t α) (F : Form Γ-t (γ > β)) (H : Form Γ-t γ) (G : Form Γ-t α) → Γ ⊢ α ∋ S (headNorm' m F H) ↔ G → Γ ⊢ α ∋ S (app F H) ↔ G
 hn-left-i' (suc m) S (lam _ F) H G p with hn-left-i m S (sub H F) G p
 hn-left-i' (suc _) S (lam _ _) _ _ _ |    p' = reduce-l {_} {_} {_} {_} {_} {_} {S} p'
 hn-left-i' 0 _ (lam _ _) _ _ p = p
 hn-left-i' zero _ (var _ _) _ _ p = p
 hn-left-i' (suc _) _ (var _ _) _ _ p = p
 hn-left-i' zero _ N _ _ p = p
 hn-left-i' (suc _) _ N _ _ p = p
 hn-left-i' zero _ A _ _ p = p
 hn-left-i' (suc _) _ A _ _ p = p
 hn-left-i' zero _ Π _ _ p = p
 hn-left-i' (suc _) _ Π _ _ p = p
 hn-left-i' zero _ i _ _ p = p
 hn-left-i' (suc _) _ i _ _ p = p
 hn-left-i' zero _ (app _ _) _ _ p = p
 hn-left-i' (suc _) _ (app _ _) _ _ p = p

hn-left : {n : ℕ} {Γ-t : Ctx n} {Γ : FSC-Ctx n Γ-t} {α : Type n} (m : ℕ) (F : Form Γ-t α) (G : Form Γ-t α) → Γ ⊢ α ∋ headNorm m F ↔ G → Γ ⊢ α ∋ F ↔ G
hn-left m F G p = hn-left-i m (λ x → x) F G p

mutual
 hn-right-i : {n : ℕ} {Γ-t : Ctx n} {Γ : FSC-Ctx n Γ-t} {α β : Type n} (m : ℕ) (S : Form Γ-t β → Form Γ-t α) (F : Form Γ-t β) (G : Form Γ-t α) → Γ ⊢ α ∋ G ↔ S (headNorm m F) → Γ ⊢ α ∋ G ↔ S F
 hn-right-i m S (app F H) G p = hn-right-i m (λ x → S (app x H)) F G (hn-right-i' m S (headNorm m F) H G p)
 hn-right-i _ _ (var _ _) _ p = p
 hn-right-i _ _ N _ p = p
 hn-right-i _ _ A _ p = p
 hn-right-i _ _ Π _ p = p
 hn-right-i _ _ i _ p = p
 hn-right-i _ _ (lam _ _) _ p = p

 hn-right-i' : {n : ℕ} {Γ-t : Ctx n} {Γ : FSC-Ctx n Γ-t} {α β γ : Type n} (m : ℕ) (S : Form Γ-t β → Form Γ-t α) (F : Form Γ-t (γ > β)) (H : Form Γ-t γ) (G : Form Γ-t α) → Γ ⊢ α ∋ G ↔ S (headNorm' m F H) → Γ ⊢ α ∋ G ↔ S (app F H)
 hn-right-i' (suc m) S (lam _ F) H G p with hn-right-i m S (sub H F) G p
 hn-right-i' (suc _) S (lam _ _) _ _ _ |    p' = reduce-r {_} {_} {_} {_} {_} {_} {S} p'
 hn-right-i' 0 _ (lam _ _) _ _ p = p
 hn-right-i' zero _ (var _ _) _ _ p = p
 hn-right-i' (suc _) _ (var _ _) _ _ p = p
 hn-right-i' zero _ N _ _ p = p
 hn-right-i' (suc _) _ N _ _ p = p
 hn-right-i' zero _ A _ _ p = p
 hn-right-i' (suc _) _ A _ _ p = p
 hn-right-i' zero _ Π _ _ p = p
 hn-right-i' (suc _) _ Π _ _ p = p
 hn-right-i' zero _ i _ _ p = p
 hn-right-i' (suc _) _ i _ _ p = p
 hn-right-i' zero _ (app _ _) _ _ p = p
 hn-right-i' (suc _) _ (app _ _) _ _ p = p

hn-right : {n : ℕ} {Γ-t : Ctx n} {Γ : FSC-Ctx n Γ-t} {α : Type n} (m : ℕ) (F : Form Γ-t α) (G : Form Γ-t α) → Γ ⊢ α ∋ G ↔ headNorm m F → Γ ⊢ α ∋ G ↔ F
hn-right m F G p = hn-right-i m (λ x → x) F G p


mutual
 hn-succ-i : {n : ℕ} {Γ-t : Ctx n} {Γ : FSC-Ctx n Γ-t} {β : Type n} (m : ℕ) (S : Form Γ-t β → Form Γ-t $o) (F : Form Γ-t β) → Γ ⊢ S (headNorm m F) → Γ ⊢ S F
 hn-succ-i m S (app F H) p = hn-succ-i m (λ x → S (app x H)) F (hn-succ-i' m S (headNorm m F) H p)
 hn-succ-i _ _ (var _ _) p = p
 hn-succ-i _ _ N p = p
 hn-succ-i _ _ A p = p
 hn-succ-i _ _ Π p = p
 hn-succ-i _ _ i p = p
 hn-succ-i _ _ (lam _ _) p = p

 hn-succ-i' : {n : ℕ} {Γ-t : Ctx n} {Γ : FSC-Ctx n Γ-t} {β γ : Type n} (m : ℕ) (S : Form Γ-t β → Form Γ-t $o) (F : Form Γ-t (γ > β)) (H : Form Γ-t γ) → Γ ⊢ S (headNorm' m F H) → Γ ⊢ S (app F H)
 hn-succ-i' (suc m) S (lam _ F) H p with hn-succ-i m S (sub H F) p
 hn-succ-i' (suc _) S (lam _ _) _ _ |    p' = reduce {_} {_} {_} {_} {_} {S} p'
 hn-succ-i' 0 _ (lam _ _) _ p = p
 hn-succ-i' zero _ (var _ _) _ p = p
 hn-succ-i' (suc _) _ (var _ _) _ p = p
 hn-succ-i' zero _ N _ p = p
 hn-succ-i' (suc _) _ N _ p = p
 hn-succ-i' zero _ A _ p = p
 hn-succ-i' (suc _) _ A _ p = p
 hn-succ-i' zero _ Π _ p = p
 hn-succ-i' (suc _) _ Π _ p = p
 hn-succ-i' zero _ i _ p = p
 hn-succ-i' (suc _) _ i _ p = p
 hn-succ-i' zero _ (app _ _) _ p = p
 hn-succ-i' (suc _) _ (app _ _) _ p = p

hn-succ : {n : ℕ} {Γ-t : Ctx n} {Γ : FSC-Ctx n Γ-t} (m : ℕ) (F : Form Γ-t $o) → Γ ⊢ headNorm m F → Γ ⊢ F
hn-succ m F p = hn-succ-i m (λ x → x) F p


mutual
 hn-ante-i : {n : ℕ} {Γ-t : Ctx n} {Γ : FSC-Ctx n Γ-t} {β : Type n} (m : ℕ) (S : Form Γ-t β → Form Γ-t $o) (F : Form Γ-t β) (G : Form Γ-t $o) → Γ , S (headNorm m F) ⊢ G → Γ , S F ⊢ G
 hn-ante-i m S (app F H) G p = hn-ante-i m (λ x → S (app x H)) F G (hn-ante-i' m S (headNorm m F) H G p)
 hn-ante-i _ _ (var _ _) _ p = p
 hn-ante-i _ _ N _ p = p
 hn-ante-i _ _ A _ p = p
 hn-ante-i _ _ Π _ p = p
 hn-ante-i _ _ i _ p = p
 hn-ante-i _ _ (lam _ _) _ p = p

 hn-ante-i' : {n : ℕ} {Γ-t : Ctx n} {Γ : FSC-Ctx n Γ-t} {β γ : Type n} (m : ℕ) (S : Form Γ-t β → Form Γ-t $o) (F : Form Γ-t (γ > β)) (H : Form Γ-t γ) (G : Form Γ-t $o) → Γ , S (headNorm' m F H) ⊢ G → Γ , S (app F H) ⊢ G
 hn-ante-i' (suc m) S (lam _ F) H G p with hn-ante-i m S (sub H F) G p
 hn-ante-i' (suc _) S (lam _ _) _ _ _ |    p' = reduce {_} {_} {_} {_} {_} {S} p'
 hn-ante-i' 0 _ (lam _ _) _ _ p = p
 hn-ante-i' zero _ (var _ _) _ _ p = p
 hn-ante-i' (suc _) _ (var _ _) _ _ p = p
 hn-ante-i' zero _ N _ _ p = p
 hn-ante-i' (suc _) _ N _ _ p = p
 hn-ante-i' zero _ A _ _ p = p
 hn-ante-i' (suc _) _ A _ _ p = p
 hn-ante-i' zero _ Π _ _ p = p
 hn-ante-i' (suc _) _ Π _ _ p = p
 hn-ante-i' zero _ i _ _ p = p
 hn-ante-i' (suc _) _ i _ _ p = p
 hn-ante-i' zero _ (app _ _) _ _ p = p
 hn-ante-i' (suc _) _ (app _ _) _ _ p = p

hn-ante : {n : ℕ} {Γ-t : Ctx n} {Γ : FSC-Ctx n Γ-t} (m : ℕ) (F : Form Γ-t $o) (G : Form Γ-t $o) → Γ , headNorm m F ⊢ G → Γ , F ⊢ G
hn-ante m F G p = hn-ante-i m (λ x → x) F G p


mutual
 hn-ante-eq-i : {n : ℕ} {Γ-t : Ctx n} {Γ : FSC-Ctx n Γ-t} {α β : Type n} (m : ℕ) (S : Form Γ-t β → Form Γ-t $o) (F : Form Γ-t β) (G H : Form Γ-t α) → Γ , S (headNorm m F) ⊢ G == H → Γ , S F ⊢ G == H
 hn-ante-eq-i m S (app F I) G H p = hn-ante-eq-i m (λ x → S (app x I)) F G H (hn-ante-eq-i' m S (headNorm m F) I G H p)
 hn-ante-eq-i _ _ (var _ _) _ _ p = p
 hn-ante-eq-i _ _ N _ _ p = p
 hn-ante-eq-i _ _ A _ _ p = p
 hn-ante-eq-i _ _ Π _ _ p = p
 hn-ante-eq-i _ _ i _ _ p = p
 hn-ante-eq-i _ _ (lam _ _) _ _ p = p

 hn-ante-eq-i' : {n : ℕ} {Γ-t : Ctx n} {Γ : FSC-Ctx n Γ-t} {α β γ : Type n} (m : ℕ) (S : Form Γ-t β → Form Γ-t $o) (F : Form Γ-t (γ > β)) (I : Form Γ-t γ) (G H : Form Γ-t α) → Γ , S (headNorm' m F I) ⊢ G == H → Γ , S (app F I) ⊢ G == H
 hn-ante-eq-i' (suc m) S (lam _ F) I G H p with hn-ante-eq-i m S (sub I F) G H p
 hn-ante-eq-i' (suc _) S (lam _ _) _ _ _ _ |    p' = reduce {_} {_} {_} {_} {_} {_} {S} p'
 hn-ante-eq-i' 0 _ (lam _ _) _ _ _ p = p
 hn-ante-eq-i' zero _ (var _ _) _ _ _ p = p
 hn-ante-eq-i' (suc _) _ (var _ _) _ _ _ p = p
 hn-ante-eq-i' zero _ N _ _ _ p = p
 hn-ante-eq-i' (suc _) _ N _ _ _ p = p
 hn-ante-eq-i' zero _ A _ _ _ p = p
 hn-ante-eq-i' (suc _) _ A _ _ _ p = p
 hn-ante-eq-i' zero _ Π _ _ _ p = p
 hn-ante-eq-i' (suc _) _ Π _ _ _ p = p
 hn-ante-eq-i' zero _ i _ _ _ p = p
 hn-ante-eq-i' (suc _) _ i _ _ _ p = p
 hn-ante-eq-i' zero _ (app _ _) _ _ _ p = p
 hn-ante-eq-i' (suc _) _ (app _ _) _ _ _ p = p

hn-ante-eq : {n : ℕ} {Γ-t : Ctx n} {Γ : FSC-Ctx n Γ-t} {α : Type n} (m : ℕ) (F : Form Γ-t $o) (G H : Form Γ-t α) → Γ , headNorm m F ⊢ G == H → Γ , F ⊢ G == H
hn-ante-eq m F G H p = hn-ante-eq-i m (λ x → x) F G H p

-- ------------------------------------

head-& : {n : ℕ} {Γ-t : Ctx n} {Γ : FSC-Ctx n Γ-t} {F₁ F₂ G₁ G₂ : Form Γ-t $o} →
 Γ ⊢ $o ∋ F₁ == F₂ → Γ ⊢ $o ∋ G₁ == G₂ →
 Γ ⊢ $o ∋ (F₁ & G₁) ↔ (F₂ & G₂)
head-& p₁ p₂ = head-app _ _ _ _ _ _ (simp (head-const _ N)) (simp (head-app _ _ _ _ _ _ (simp (head-app _ _ _ _ _ _ (simp (head-const _ A)) (simp (head-app _ _ _ _ _ _ (simp (head-const _ N)) p₁)))) (simp (head-app _ _ _ _ _ _ (simp (head-const _ N)) p₂))))

head-|| : {n : ℕ} {Γ-t : Ctx n} {Γ : FSC-Ctx n Γ-t} {F₁ F₂ G₁ G₂ : Form Γ-t $o} →
 Γ ⊢ $o ∋ F₁ == F₂ → Γ ⊢ $o ∋ G₁ == G₂ →
 Γ ⊢ $o ∋ (F₁ || G₁) ↔ (F₂ || G₂)
head-|| p₁ p₂ = head-app _ _ _ _ _ _ (simp (head-app _ _ _ _ _ _ (simp (head-const _ A)) p₁)) p₂

head-=> : {n : ℕ} {Γ-t : Ctx n} {Γ : FSC-Ctx n Γ-t} {F₁ F₂ G₁ G₂ : Form Γ-t $o} →
 Γ ⊢ $o ∋ F₁ == F₂ → Γ ⊢ $o ∋ G₁ == G₂ →
 Γ ⊢ $o ∋ (F₁ => G₁) ↔ (F₂ => G₂)
head-=> p₁ p₂ = head-app _ _ _ _ _ _ (simp (head-app _ _ _ _ _ _ (simp (head-const _ A)) (simp (head-app _ _ _ _ _ _ (simp (head-const _ N)) p₁)))) p₂

head-~ : {n : ℕ} {Γ-t : Ctx n} {Γ : FSC-Ctx n Γ-t} {F₁ F₂ : Form Γ-t $o} →
 Γ ⊢ $o ∋ F₁ == F₂ →
 Γ ⊢ $o ∋ (~ F₁) ↔ (~ F₂)
head-~ p = head-app _ _ _ _ _ _ (simp (head-const _ N)) p

head-== : {n : ℕ} {Γ-t : Ctx n} {Γ : FSC-Ctx n Γ-t} {α : Type n} {F₁ F₂ G₁ G₂ : Form Γ-t α} →
 Γ ⊢ α ∋ F₁ == F₂ → Γ ⊢ α ∋ G₁ == G₂ →
 Γ ⊢ $o ∋ (F₁ == G₁) ↔ (F₂ == G₂)
head-== p₁ p₂ = head-app _ _ _ _ _ _ (simp (head-app _ _ _ _ _ _ (simp (head-const _ _)) p₁)) p₂
