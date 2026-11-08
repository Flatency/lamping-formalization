import Lamping.Lambda.Beta
namespace Lamping.Lambda

/-- A red node is an initially selected redex; ordinary applications never
    become active merely because substitution exposes a lambda. -/
inductive Marked where
  | var : Nat → Marked
  | lam : Marked → Marked
  | app : List Path → Marked → Marked → Marked
  | red : List Path → Marked → Marked → Marked
  deriving DecidableEq, Repr

namespace Marked

def erase : Marked → Term
  | .var i => .var i
  | .lam b => .lam (erase b)
  | .app _ f a => .app (erase f) (erase a)
  | .red _ b a => .app (.lam (erase b)) (erase a)

def rename (ρ : Nat → Nat) : Marked → Marked
  | .var i => .var (ρ i)
  | .lam b => .lam (rename (liftRen ρ) b)
  | .app l f a => .app l (rename ρ f) (rename ρ a)
  | .red l b a => .red l (rename (liftRen ρ) b) (rename ρ a)

def liftSub (σ : Nat → Marked) : Nat → Marked
  | 0 => .var 0
  | i+1 => rename Nat.succ (σ i)

def subst (σ : Nat → Marked) : Marked → Marked
  | .var i => σ i
  | .lam b => .lam (subst (liftSub σ) b)
  | .app l f a => .app l (subst σ f) (subst σ a)
  | .red l b a => .red l (subst (liftSub σ) b) (subst σ a)

theorem rename_congr {ρ τ : Nat → Nat} (h : ∀ i, ρ i = τ i) (t : Marked) : rename ρ t = rename τ t := by
  cases funext h
  rfl

@[simp] theorem rename_id (t : Marked) : rename id t = t := by
  induction t with
  | var i => rfl
  | lam b hb =>
    have h : liftRen id = id := by funext i; cases i <;> rfl
    simp [rename, h, hb]
  | app l f a hf ha => simp [rename, hf, ha]
  | red l b a hb ha =>
    have h : liftRen id = id := by funext i; cases i <;> rfl
    simp [rename, h, hb, ha]

theorem rename_comp (τ ρ : Nat → Nat) (t : Marked) : rename τ (rename ρ t) = rename (τ ∘ ρ) t := by
  induction t generalizing τ ρ with
  | var i => rfl
  | app l f a hf ha => simp [rename, hf, ha]
  | lam b hb =>
    simp only [rename, hb]
    congr 1
    apply rename_congr
    intro i
    cases i <;> rfl
  | red l b a hb ha =>
    simp only [rename, hb, ha]
    congr 1
    apply rename_congr
    intro i
    cases i <;> rfl

theorem rename_subst (ρ : Nat → Nat) (σ : Nat → Marked) (t : Marked) :
    rename ρ (subst σ t) = subst (fun i => rename ρ (σ i)) t := by
  induction t generalizing ρ σ with
  | var i => rfl
  | app l f a hf ha => simp [rename, subst, hf, ha]
  | lam b hb =>
    simp only [subst, rename, hb]
    congr 1; congr 1; funext i
    cases i with
    | zero => rfl
    | succ i => simp [liftSub, rename_comp, Function.comp_def, liftRen]
  | red l b a hb ha =>
    simp only [subst, rename, hb, ha]
    congr 1; congr 1; funext i
    cases i with
    | zero => rfl
    | succ i => simp [liftSub, rename_comp, Function.comp_def, liftRen]

theorem subst_rename (σ : Nat → Marked) (ρ : Nat → Nat) (t : Marked) :
    subst σ (rename ρ t) = subst (fun i => σ (ρ i)) t := by
  induction t generalizing σ ρ with
  | var i => rfl
  | app l f a hf ha => simp [rename, subst, hf, ha]
  | lam b hb =>
    simp only [subst, rename, hb]
    congr 1; congr 1; funext i; cases i <;> rfl
  | red l b a hb ha =>
    simp only [subst, rename, hb, ha]
    congr 1; congr 1; funext i; cases i <;> rfl

@[simp] theorem subst_id (t : Marked) : subst Marked.var t = t := by
  induction t with
  | var i => rfl
  | app l f a hf ha => simp [subst, hf, ha]
  | lam b hb =>
    have h : liftSub Marked.var = Marked.var := by funext i; cases i <;> rfl
    simp [subst, h, hb]
  | red l b a hb ha =>
    have h : liftSub Marked.var = Marked.var := by funext i; cases i <;> rfl
    simp [subst, h, hb, ha]

theorem subst_comp (τ σ : Nat → Marked) (t : Marked) :
    subst τ (subst σ t) = subst (fun i => subst τ (σ i)) t := by
  induction t generalizing τ σ with
  | var i => rfl
  | app l f a hf ha => simp [subst, hf, ha]
  | lam b hb =>
    simp only [subst, hb]
    congr 1; congr 1; funext i
    cases i with
    | zero => rfl
    | succ i => simp [liftSub, subst_rename, rename_subst]
  | red l b a hb ha =>
    simp only [subst, hb, ha]
    congr 1; congr 1; funext i
    cases i with
    | zero => rfl
    | succ i => simp [liftSub, subst_rename, rename_subst]

def single (a : Marked) : Nat → Marked
  | 0 => a
  | i+1 => .var i

def contract (b a : Marked) := subst (single a) b

@[simp] theorem erase_rename (ρ) (t : Marked) : erase (rename ρ t) = Lambda.rename ρ (erase t) := by
  induction t generalizing ρ with
  | var i => rfl
  | lam b hb => simp [rename, erase, Lambda.rename, hb]
  | app l f a hf ha => simp [rename, erase, Lambda.rename, hf, ha]
  | red l b a hb ha => simp [rename, erase, Lambda.rename, hb, ha]

@[simp] theorem erase_subst (σ) (t : Marked) : erase (subst σ t) = Lambda.subst (fun i => erase (σ i)) (erase t) := by
  induction t generalizing σ with
  | var i => rfl
  | app l f a hf ha => simp [subst, erase, Lambda.subst, hf, ha]
  | lam b hb =>
    simp only [subst, erase, Lambda.subst, hb]
    congr 1; congr 1; funext i
    cases i <;> simp [liftSub, Lambda.liftSub, erase]
  | red l b a hb ha =>
    simp only [subst, erase, Lambda.subst, hb, ha]
    congr 1; congr 1; congr 1; funext i
    cases i <;> simp [liftSub, Lambda.liftSub, erase]

@[simp] theorem erase_contract (b a) : erase (contract b a) = Lambda.contract (erase b) (erase a) := by
  simp only [contract, erase_subst, Lambda.contract]
  congr 1; funext i; cases i <;> rfl

inductive Step : Marked → Marked → Prop where
  | root (l b a) : Step (.red l b a) (contract b a)
  | lam : Step b b' → Step (.lam b) (.lam b')
  | appL : Step f f' → Step (.app l f a) (.app l f' a)
  | appR : Step a a' → Step (.app l f a) (.app l f a')
  | redL : Step b b' → Step (.red l b a) (.red l b' a)
  | redR : Step a a' → Step (.red l b a) (.red l b a')

theorem Step.erase (h : Step t u) : Beta t.erase u.erase := by
  induction h with
  | root l b a => simpa using Beta.root b.erase a.erase
  | lam h ih => exact Beta.body ih
  | appL h ih => exact Beta.fn ih
  | appR h ih => exact Beta.arg ih
  | redL h ih => exact Beta.fn (Beta.body ih)
  | redR h ih => exact Beta.arg ih

end Marked
end Lamping.Lambda

