import Lamping.Lambda.SingleContraction
import Lamping.Lambda.NoTagTransport
namespace Lamping.Lambda

/-- Every complete development of a valid singleton contracts that very
occurrence exactly once; this controls all development schedules. -/
theorem ParallelStep.singleton_paths (h : ParallelStep [p] t u) (r : RedexOcc t) (hp : r.val=p) :
    h.paths=[p] := by
  rcases h with ⟨ps,target,complete,erase⟩
  have hd := (Marked.completeOld_iff [p] t).mp complete
  have active : p∈Marked.activePositions (Marked.mark [p] t) := by
    rw [Marked.active_mark]
    refine ⟨by simp,?_⟩
    rw [←hp]
    exact (mem_redexPositions t r.val).mpr r.property
  have only : ∀ q, q∈Marked.activePositions (Marked.mark [p] t) → q=p := by
    intro q hq
    exact List.mem_singleton.mp ((Marked.active_mark [p] t q).mp hq).1
  cases hd.1 with
  | nil =>
    obtain ⟨v,step⟩ := Marked.active_has_step active
    exact False.elim ((Marked.normal_iff_no_step _).mp hd.2 ⟨v,step.step⟩)
  | cons step rest =>
    have eq := only _ step.active
    subst_vars
    have normal := step.single_normal only
    cases rest with
    | nil => rfl
    | cons next tail => exact False.elim ((Marked.normal_iff_no_step _).mp normal ⟨_,next.step⟩)

/-- Outside a contracted subtree an old redex has precisely its unchanged
position as residual, including when it is a strict ancestor of the step. -/
theorem BetaAt.outside_residual_iff (h : BetaAt t p u) (r : RedexOcc t)
    (outside : ¬ ∃ tail, r.val=p++tail) (s : RedexOcc u) :
    (singleContraction h).derivation.Residual r s ↔ r.val=s.val := by
  have tracking := (singleContraction h).tracked
  change Marked.History [p] (Marked.mark [] t) _ at tracking
  cases tracking with
  | cons step rest =>
    cases rest
    have absent : ∀ tail, p++tail ∉ Marked.tracePositions r.val (Marked.mark [] t) := by
      intro tail hit
      exact outside ⟨tail,((Marked.initial_residual [] t r (p++tail)).mp hit).symm⟩
    rw [Derivation.residual_iff_tracking _ (.cons step (.nil _)),step.trace_outside absent,
      Marked.initial_residual]
    exact eq_comm
end Lamping.Lambda
