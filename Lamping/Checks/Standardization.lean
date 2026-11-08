import Lamping.Lambda.StandardizationExistence
import Lamping.Lambda.StandardizationExtraction
import Lamping.Lambda.StandardizationGeneral
import Lamping.Lambda.PermutationResidual
import Lamping.Lambda.RootResidualPaths
namespace Lamping.Checks.Standardization
open Lambda
abbrev delta : Term := .lam (.app (.var 0) (.var 0))
abbrev omegaTerm : Term := .app delta delta
def omegaStep : BetaAt omegaTerm [] omegaTerm :=
  ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
def omegaRedex : RedexOcc omegaTerm := ⟨[],⟨omegaTerm,rfl,True.intro⟩⟩
example : ¬PermEq (ParallelHistory.single (singleContraction omegaStep)) (.nil omegaTerm) := by
  intro eq
  have gone : ¬(singleContraction omegaStep).derivation.Residual omegaRedex omegaRedex := by
    rw [←rootContraction_eq_single omegaStep,root_residual_iff]
    simp [omegaRedex]
  have preserved := (eq.residual omegaRedex omegaRedex).mpr ((Derivation.residual_nil _ _).mpr rfl)
  exact gone (by simpa only [ParallelHistory.single_derivation] using preserved)
example (h : ParallelStep F t u) (r : RedexOcc t) (hr : LeftmostSelected F r) :
    Standard (ParallelHistory.single h) := Standard.single_step h r hr
example (h : ParallelStep F t u) (r : RedexOcc t) (hr : r.val∈F) :
    ∃ (v : Term) (head : BetaAt t r.val v)
      (tail : ParallelStep ((singleContraction head).residualSet F) v u),
      PermEq (ParallelHistory.single h)
        ((ParallelHistory.single (singleContraction head)).append (.single tail)) :=
  h.selected_factor r hr
example (h : ParallelStep F t u) :
    ∃ σ : ParallelHistory t u, Standard σ ∧ PermEq (ParallelHistory.single h) σ :=
  standardize_single h
def invalidSelectionStep : ParallelStep [[.fn]] (.var 0) (.var 0) :=
  ⟨[],.var 0,⟨.nil _,rfl⟩,rfl⟩
example : PermEq (.single invalidSelectionStep) (.nil (.var 0)) := by
  apply PermEq.no_actual_selection
  rintro ⟨p,redex,lookup,isRedex⟩ member
  cases p with
  | nil => cases lookup; cases isRedex
  | cons s p => cases s <;> cases lookup
example : ∃ σ : ParallelHistory (.var 0) (.var 0), Standard σ ∧
    PermEq (.single invalidSelectionStep) σ := standardize_single invalidSelectionStep
example (h : BetaAt t p u) (s : RedexOcc t) (before : LeftOf s.val p) (q : RedexOcc u) :
    (singleContraction h).derivation.Residual s q ↔ q.val=s.val := h.left_residual_iff s before q
#print axioms Standard.single_step
#print axioms ParallelStep.selected_factor
#print axioms standardize_single
#print axioms BetaAt.left_residual_iff
#print axioms BetaAt.left_residual_exists
example (h : Marked.StepAt p m m')
    (right : ∀ q∈Marked.activePositions m, LeftOf cut q) :
    ∀ q∈Marked.activePositions m', LeftOf cut q := h.right_cut right
example (h : ParallelStep F t u) (s : RedexOcc t)
    (right : ∀ r : RedexOcc t, r.val∈F → LeftOf s.val r.val) (q : RedexOcc u) :
    h.derivation.Residual s q ↔ q.val=s.val := h.left_residual_iff s right q
#print axioms Marked.StepAt.right_cut
#print axioms ParallelStep.left_residual_iff
#print axioms ParallelStep.left_residual_exists
example (h : ParallelStep F t u) (s : RedexOcc t)
    (right : ∀ r : RedexOcc t, r.val∈F → LeftOf s.val r.val)
    (source : BetaAt t s.val v) (later : BetaAt u s.val w) :
    ∃ after : ParallelStep ((singleContraction source).residualSet F) v w,
      PermEq ((ParallelHistory.single h).append (.single (singleContraction later)))
        ((ParallelHistory.single (singleContraction source)).append (.single after)) :=
  h.pull_left_step s right source later
#print axioms ParallelStep.pull_left_step
example (ρ : ParallelHistory t u) (s : RedexOcc t) (right : RightHistory s.val ρ)
    (last : BetaAt u s.val w) :
    ∃ (v : Term) (source : BetaAt t s.val v) (tail : ParallelHistory v w),
      PermEq (ρ.append (.single (singleContraction last)))
        ((ParallelHistory.single (singleContraction source)).append tail) ∧ tail.length=ρ.length :=
  right.pull_step s rfl last
example (n : Nat) : WellFounded (HistoryCost.Lt n) := HistoryCost.wellFounded n
example (ρ : ParallelHistory t u) (s : RedexOcc t) (right : RightHistory s.val ρ)
    (step : ParallelStep G u v) (selected : s.val∈G) (suffix : ParallelHistory v w) :
    ∃ (z : Term) (source : BetaAt t s.val z) (tail : ParallelHistory z w),
      PermEq (ρ.append (.cons step suffix)) ((ParallelHistory.single (singleContraction source)).append tail) ∧
      tail.length=(ρ.append (.cons step suffix)).length ∧
      HistoryCost.ListLt tail.costs (ρ.append (.cons step suffix)).costs :=
  right.pull_selected s rfl step selected suffix
#print axioms RightHistory.pull_step
#print axioms RightHistory.pull_selected
#print axioms HistoryCost.wellFounded
example (ρ : ParallelHistory t u) :
    ∃ σ : ParallelHistory t u, Standard σ ∧ PermEq ρ σ := standardization_exists ρ
example (ρ : ParallelHistory t u) :
    ∃ σ : ParallelHistory t u, Atomic σ ∧ Standard σ ∧ PermEq ρ σ :=
  atomic_standardization_exists ρ
example (ρ σ : ParallelHistory t u) (s : RedexOcc t)
    (safe : RightHistory s.val ρ) (perm : PermEq ρ σ) : RightHistory s.val σ :=
  RightHistory.permutation s safe perm
example (ρ : ParallelHistory t u) (used : ∃ r : RedexOcc t, UsedSource ρ r) :
    ∃ (s : RedexOcc t) (z : Term) (head : BetaAt t s.val z) (tail : ParallelHistory z u),
      PermEq ρ ((ParallelHistory.single (singleContraction head)).append tail) ∧
      tail.length=ρ.length ∧ HistoryCost.ListLt tail.costs ρ.costs ∧
      ∀ r : RedexOcc t, LeftOf r.val s.val → RightHistory r.val ρ :=
  ρ.extract_minimal used
/-- A non-normalizing term and a genuine two-contraction history remain in
the unrestricted existence theorem; source normalization is no premise. -/
example : ∃ σ : ParallelHistory omegaTerm omegaTerm, Standard σ ∧
    PermEq (.cons (singleContraction omegaStep) (.single (singleContraction omegaStep))) σ :=
  standardization_exists _
/-- Invalid names may occur throughout a history, not only in a singleton. -/
example : PermEq (.cons invalidSelectionStep (.single invalidSelectionStep)) (.nil (.var 0)) := by
  have one : PermEq (.single invalidSelectionStep) (.nil (.var 0)) := by
    apply PermEq.no_actual_selection invalidSelectionStep
    rintro ⟨p,redex,lookup,isRedex⟩ member
    cases p with
    | nil => cases lookup; cases isRedex
    | cons s p => cases s <;> cases lookup
  exact PermEq.comp one one
#print axioms ParallelHistory.right_or_kills_left
#print axioms RightHistory.permutation
#print axioms ParallelHistory.no_used
#print axioms ParallelHistory.extract_minimal
#print axioms standardization_exists
#print axioms atomic_standardization_exists
end Lamping.Checks.Standardization
