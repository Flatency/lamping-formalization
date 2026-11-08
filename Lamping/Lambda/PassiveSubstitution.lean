import Lamping.Lambda.ParallelPrefixResidualSet
import Lamping.Lambda.RootResidualPaths
namespace Lamping.Lambda.Marked

/-- A substitution value with no activity or old application identities. -/
def plain : Term → Marked
  | .var i => .var i
  | .lam b => .lam (plain b)
  | .app f a => .app [] (plain f) (plain a)

@[simp] theorem erase_plain (t : Term) : (plain t).erase=t := by
  induction t <;> simp_all [plain,erase]

theorem plain_normal (t : Term) : Normal (plain t) := by
  induction t <;> simp_all [plain,Normal]

@[simp] theorem plain_trace (r : Path) (t : Term) : tracePositions r (plain t)=[] := by
  induction t <;> simp_all [plain,tracePositions]

theorem StepAt.substitute (h : StepAt p t u) (σ : Nat → Marked) :
    StepAt p (subst σ t) (subst σ u) := by
  induction h generalizing σ with
  | root l b a => simpa only [subst,subst_contract] using StepAt.root l (subst (liftSub σ) b) (subst σ a)
  | lam h ih => exact .lam (ih _)
  | appL h ih => exact .appL (ih _)
  | appR h ih => exact .appR (ih _)
  | redL h ih => exact .redL (ih _)
  | redR h ih => exact .redR (ih _)

theorem ReductionAt.substitute (h : ReductionAt p t u) (σ : Nat → Marked) :
    ReductionAt p (subst σ t) (subst σ u) := by
  induction h generalizing σ with
  | appRoot l b a => simpa only [subst,subst_contract] using ReductionAt.appRoot l (subst (liftSub σ) b) (subst σ a)
  | redRoot l b a => simpa only [subst,subst_contract] using ReductionAt.redRoot l (subst (liftSub σ) b) (subst σ a)
  | lam h ih => exact .lam (ih _)
  | appL h ih => exact .appL (ih _)
  | appR h ih => exact .appR (ih _)
  | redL h ih => exact .redL (ih _)
  | redR h ih => exact .redR (ih _)

theorem History.substitute (h : History ps t u) (σ : Nat → Marked) :
    History ps (subst σ t) (subst σ u) := by
  induction h with
  | nil => exact .nil _
  | cons head tail ih => exact .cons (head.substitute σ) ih

theorem RelativeHistory.substitute (h : RelativeHistory ps t u) (σ : Nat → Marked) :
    RelativeHistory ps (subst σ t) (subst σ u) := by
  induction h with
  | nil => exact .nil _
  | cons head tail ih => exact .cons (head.substitute σ) ih

theorem trace_subst_untagged (t : Marked) (σ : Nat → Marked)
    (empty : ∀ i,tracePositions r (σ i)=[]) : tracePositions r (subst σ t)=tracePositions r t := by
  induction t generalizing σ with
  | var i => exact empty i
  | app l f a hf ha => simp only [subst,tracePositions,hf σ empty,ha σ empty]
  | lam b ih =>
    have lifted : ∀ i,tracePositions r (liftSub σ i)=[] := by
      intro i; cases i with
      | zero => rfl
      | succ i => simpa only [liftSub,trace_rename] using empty i
    simp only [subst,tracePositions,ih _ lifted]
  | red l b a hb ha =>
    have lifted : ∀ i,tracePositions r (liftSub σ i)=[] := by
      intro i; cases i with
      | zero => rfl
      | succ i => simpa only [liftSub,trace_rename] using empty i
    simp only [subst,tracePositions,hb _ lifted,ha σ empty]

theorem active_subst_inactive (t : Marked) (σ : Nat → Marked)
    (inactive : ∀ i,Normal (σ i)) : activePositions (subst σ t)=activePositions t := by
  induction t generalizing σ with
  | var i => exact (normal_iff_active_empty _).mp (inactive i)
  | app l f a hf ha => simp only [subst,activePositions,hf σ inactive,ha σ inactive]
  | lam b ih =>
    have lifted : ∀ i,Normal (liftSub σ i) := by
      intro i; cases i with
      | zero => trivial
      | succ i => exact normal_rename (inactive i) _
    simp only [subst,activePositions,ih _ lifted]
  | red l b a hb ha =>
    have lifted : ∀ i,Normal (liftSub σ i) := by
      intro i; cases i with
      | zero => trivial
      | succ i => exact normal_rename (inactive i) _
    simp only [subst,activePositions,hb _ lifted,ha σ inactive]
end Lamping.Lambda.Marked
