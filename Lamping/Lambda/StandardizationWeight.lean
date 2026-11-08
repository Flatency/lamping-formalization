import Lamping.Lambda.SingleContraction
import Lamping.Lambda.ParallelMoves
namespace Lamping.Lambda

theorem Marked.weight_skeleton (e : Nat → Nat) (t : Marked) :
    Marked.weight e t.skeleton = Marked.weight e t := by
  induction t generalizing e <;> simp_all [Marked.skeleton,Marked.weight]

/-- Contracting any actually selected redex strictly lowers the old-set
development weight, after selecting precisely its actual residual image.
The environment is arbitrary; no rank inequality is assumed. -/
theorem BetaAt.selected_residual_weight_lt (h : BetaAt t p u)
    (selected : p∈F) (e : Nat → Nat) :
    Marked.weight e (Marked.mark ((singleContraction h).residualSet F) u) <
      Marked.weight e (Marked.mark F t) := by
  have tracking := ((Marked.completeOld_iff [p] t).mp (singleContraction h).complete).1.general
  change Marked.History [p] (Marked.mark [p] t) (singleContraction h).markedTarget at tracking
  have reselected := tracking.reselect (Marked.valid_mark [p] t) F
  rw [Marked.reselect_mark] at reselected
  have active : p∈Marked.activePositions (Marked.mark F t) :=
    (Marked.active_mark F t p).mpr ⟨selected,(mem_redexPositions t p).mpr h.redex⟩
  have shapes := congrArg (Marked.weight e) ((singleContraction h).residual_skeleton F)
  simp only [Marked.weight_skeleton] at shapes
  rw [← shapes]
  cases reselected with
  | cons first rest =>
    cases rest
    exact (first.active_stepAt active).step.weight_lt e

end Lamping.Lambda
