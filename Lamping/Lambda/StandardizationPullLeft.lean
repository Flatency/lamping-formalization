import Lamping.Lambda.StandardizationRightCut
import Lamping.Lambda.StandardizationFactorization
import Lamping.Lambda.FiniteSelectionReindex
namespace Lamping.Lambda
/-- A left source singleton has exactly the same extensional singleton residual
selection after a right-hand complete development, not just a chosen witness. -/
theorem ParallelStep.left_residualSet (h : ParallelStep F t u) (s : RedexOcc t)
    (right : ∀ r : RedexOcc t, r.val∈F → LeftOf s.val r.val) (p : Path) :
    p∈h.residualSet [s.val] ↔ p=s.val := by
  have initial : ∀ p∈Marked.activePositions (Marked.mark F t), LeftOf s.val p := by
    intro p hp
    obtain ⟨selected,valid⟩ := (Marked.active_mark F t p).mp hp
    exact right ⟨p,(mem_redexPositions t p).mp valid⟩ selected
  have paths := ((Marked.completeOld_iff F t).mp h.complete).1.right_paths initial
  have fixed := h.tracked.trace_fixed_right paths (fun p hp => (Marked.initial_residual [] t s p).mp hp)
  change p∈Marked.setResidualPositions [s.val] h.markedTarget ↔ _
  simp only [Marked.setResidualPositions,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [←Marked.passive_trace,fixed]
  exact Marked.initial_residual [] t s p
/-- Pull an actual later contraction of a left source redex across an arbitrary
right-hand parallel step. The common target and residual development are built
by real parallel moves; no target-transport certificate is assumed. -/
theorem ParallelStep.pull_left_step (h : ParallelStep F t u) (s : RedexOcc t)
    (right : ∀ r : RedexOcc t, r.val∈F → LeftOf s.val r.val)
    (source : BetaAt t s.val v) (later : BetaAt u s.val w) :
    ∃ after : ParallelStep ((singleContraction source).residualSet F) v w,
      PermEq ((ParallelHistory.single h).append (.single (singleContraction later)))
        ((ParallelHistory.single (singleContraction source)).append (.single after)) := by
  obtain ⟨z,afterH,afterS,moves⟩ := parallel_moves h (singleContraction source)
  have sameSelection : ∀ p, p∈h.residualSet [s.val] ↔ p∈[s.val] := by
    intro p
    rw [h.left_residualSet s right,List.mem_singleton]
  have target : z=w := afterH.endpoint_selection (singleContraction later) sameSelection
  subst z
  have realization := PermEq.selection (singleContraction later) afterH (fun p => (sameSelection p).symm)
  exact ⟨afterS,.trans (.comp (.refl _) realization) moves⟩
end Lamping.Lambda
