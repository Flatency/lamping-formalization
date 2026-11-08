import Lamping.Lambda.FiniteSelections
import Lamping.Lambda.SingleContraction
namespace Lamping.Lambda
/-- Complete development removes every residual of each selected subcollection. -/
theorem ParallelStep.residualSet_subset_empty (h : ParallelStep F t u)
    (subset : ∀ p∈G, p∈F) : h.residualSet G=[] := by
  have impossible (p : Path) (hp : p∈h.residualSet G) : False := by
    obtain ⟨r,hr,trace⟩ := (Marked.mem_setResidualPositions G _ p).mp hp
    have selected := (Marked.mem_setResidualPositions F _ p).mpr ⟨r,subset r hr,trace⟩
    rw [h.complete.2] at selected
    exact List.not_mem_nil selected
  cases eq : h.residualSet G with
  | nil => rfl
  | cons p ps => exact False.elim (impossible p (by simp [eq]))

theorem RedexOcc.contract_exists (r : RedexOcc t) : ∃ u, BetaAt t r.val u := by
  obtain ⟨redex,lookup,isRedex⟩ := r.property
  cases redex with
  | var i => cases isRedex
  | lam b => cases isRedex
  | app f a =>
    cases f with
    | var i => cases isRedex
    | app f x => cases isRedex
    | lam b =>
      obtain ⟨u,replace,_⟩ := replaceAt_lookup lookup (contract b a)
      exact ⟨u,b,a,lookup,replace⟩
/-- Factor any actual selected occurrence to the front of its complete parallel
step, retaining a real residual development and the original PermEq generators. -/
theorem ParallelStep.selected_factor (h : ParallelStep F t u) (r : RedexOcc t)
    (selected : r.val∈F) :
    ∃ (v : Term) (head : BetaAt t r.val v)
      (tail : ParallelStep ((singleContraction head).residualSet F) v u),
      PermEq (ParallelHistory.single h)
        ((ParallelHistory.single (singleContraction head)).append (.single tail)) := by
  obtain ⟨v,head⟩ := r.contract_exists
  have empty : h.residualSet [r.val]=[] :=
    h.residualSet_subset_empty (fun p hp => by have eq:=List.mem_singleton.mp hp; subst p; exact selected)
  obtain ⟨w,afterH,afterR,moves⟩ := parallel_moves h (singleContraction head)
  have endpoint : w=u := by
    have a : ParallelStep [] u w := by rw [←empty]; exact afterH
    exact a.endpoint (ParallelStep.empty u)
  subst w
  have delete := PermEq.comp (PermEq.refl (ParallelHistory.single h)) (PermEq.empty_of_selection afterH empty)
  rw [ParallelHistory.append_nil] at delete
  exact ⟨v,head,afterR,.trans (.symm delete) moves⟩
end Lamping.Lambda
