import Lamping.Lambda.Syntax
namespace Lamping.Lambda

def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i+1 => ρ i + 1

def rename (ρ : Nat → Nat) : Term → Term
  | .var i => .var (ρ i)
  | .app f a => .app (rename ρ f) (rename ρ a)
  | .lam b => .lam (rename (liftRen ρ) b)

def liftSub (σ : Nat → Term) : Nat → Term
  | 0 => .var 0
  | i+1 => rename Nat.succ (σ i)

def subst (σ : Nat → Term) : Term → Term
  | .var i => σ i
  | .app f a => .app (subst σ f) (subst σ a)
  | .lam b => .lam (subst (liftSub σ) b)

theorem rename_congr {ρ τ : Nat → Nat} (h : ∀ i, ρ i = τ i) (t : Term) : rename ρ t = rename τ t := by
  cases funext h
  rfl

@[simp] theorem rename_id (t : Term) : rename id t = t := by
  induction t with
  | var i => rfl
  | app f a hf ha => simp [rename, hf, ha]
  | lam b hb =>
    have h : liftRen id = id := by funext i; cases i <;> rfl
    simp [rename, h, hb]

theorem rename_comp (τ ρ : Nat → Nat) (t : Term) : rename τ (rename ρ t) = rename (τ ∘ ρ) t := by
  induction t generalizing τ ρ with
  | var i => rfl
  | app f a hf ha => simp [rename, hf, ha]
  | lam b hb =>
    simp only [rename, hb]
    congr 1
    apply rename_congr
    intro i
    cases i <;> rfl

theorem rename_subst (ρ : Nat → Nat) (σ : Nat → Term) (t : Term) :
    rename ρ (subst σ t) = subst (fun i => rename ρ (σ i)) t := by
  induction t generalizing ρ σ with
  | var i => rfl
  | app f a hf ha => simp [rename, subst, hf, ha]
  | lam b hb =>
    simp only [subst, rename, hb]
    congr 1
    congr 1
    funext i
    cases i with
    | zero => rfl
    | succ i => simp [liftSub, rename_comp, Function.comp_def, liftRen]

theorem subst_rename (σ : Nat → Term) (ρ : Nat → Nat) (t : Term) :
    subst σ (rename ρ t) = subst (fun i => σ (ρ i)) t := by
  induction t generalizing σ ρ with
  | var i => rfl
  | app f a hf ha => simp [rename, subst, hf, ha]
  | lam b hb =>
    simp only [subst, rename, hb]
    congr 1
    congr 1
    funext i
    cases i <;> rfl

@[simp] theorem subst_id (t : Term) : subst Term.var t = t := by
  induction t with
  | var i => rfl
  | app f a hf ha => simp [subst, hf, ha]
  | lam b hb =>
    have h : liftSub Term.var = Term.var := by funext i; cases i <;> rfl
    simp [subst, h, hb]

theorem subst_comp (τ σ : Nat → Term) (t : Term) :
    subst τ (subst σ t) = subst (fun i => subst τ (σ i)) t := by
  induction t generalizing τ σ with
  | var i => rfl
  | app f a hf ha => simp [subst, hf, ha]
  | lam b hb =>
    simp only [subst, hb]
    congr 1
    congr 1
    funext i
    cases i with
    | zero => rfl
    | succ i => simp [liftSub, subst_rename, rename_subst]

theorem scoped_rename {t : Term} {n m : Nat} (ht : Scoped n t)
    (hρ : ∀ i, i < n → ρ i < m) : Scoped m (rename ρ t) := by
  induction t generalizing n m ρ with
  | var i => exact hρ i ht
  | app f a hf ha => exact ⟨hf ht.1 hρ, ha ht.2 hρ⟩
  | lam b hb =>
    apply hb ht
    intro i hi
    cases i with
    | zero => exact Nat.zero_lt_succ m
    | succ i => exact Nat.succ_lt_succ (hρ i (Nat.lt_of_succ_lt_succ hi))

theorem scoped_subst {t : Term} {n m : Nat} (ht : Scoped n t)
    (hσ : ∀ i, i < n → Scoped m (σ i)) : Scoped m (subst σ t) := by
  induction t generalizing n m σ with
  | var i => exact hσ i ht
  | app f a hf ha => exact ⟨hf ht.1 hσ, ha ht.2 hσ⟩
  | lam b hb =>
    apply hb ht
    intro i hi
    cases i with
    | zero => exact Nat.zero_lt_succ m
    | succ i => exact scoped_rename (hσ i (Nat.lt_of_succ_lt_succ hi)) (fun j hj => Nat.succ_lt_succ hj)
end Lamping.Lambda

