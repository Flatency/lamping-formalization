import Lamping.Lambda.PermutationCancellation
import Lamping.Lambda.StandardizationProtection
namespace Lamping.Checks.PermutationCancellation
open Lambda

example {a b : ParallelHistory t v} (perm : PermEq a b) (h : ParallelStep F t U) (k : ParallelStep G t U)
    (same : ∀p,p∈F ↔ p∈G) (valid : ∀p∈F,∃z,subtermAt t p=some z ∧ IsRedex z)
    {left : ParallelHistory U V} {right : ParallelHistory U W}
    {lastLeft : ParallelStep K v V} {lastRight : ParallelStep L v W}
    (rowLeft : StepProjection h a left lastLeft) (rowRight : StepProjection k b right lastRight) :
    ∃eq : V=W,PermEq (eq ▸ left) right := perm.projection_coherence h k same valid rowLeft rowRight

abbrev delta : Term := .lam (.app (.var 0) (.var 0))
abbrev omegaTerm : Term := .app delta delta
def omegaBeta : BetaAt omegaTerm [] omegaTerm := ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
theorem one_not_nil : ¬PermEq (.single (singleContraction omegaBeta)) (.nil omegaTerm) := by
  intro perm
  let old : RedexOcc omegaTerm := ⟨[],omegaBeta.redex⟩
  have alive := (perm.residual old old).mpr ((Derivation.residual_nil old old).mpr rfl)
  exact (singleContraction omegaBeta).no_selected_residual old (by simp [old]) old
    (by simpa only [ParallelHistory.single_derivation] using alive)
/-- Repeating an actual self-loop beta cannot be confused with its tail by
the new cancellation theorem or by coinciding endpoints. -/
example : ¬PermEq
    ((ParallelHistory.single (singleContraction omegaBeta)).append (.single (singleContraction omegaBeta)))
    ((ParallelHistory.single (singleContraction omegaBeta)).append (.nil omegaTerm)) := by
  intro perm
  exact one_not_nil (perm.cancel_beta_head omegaBeta)
example : PermEq (.single (singleContraction omegaBeta)) (.single (singleContraction omegaBeta)) :=
  (PermEq.refl ((ParallelHistory.single (singleContraction omegaBeta)).append (.single (singleContraction omegaBeta)))).cancel_beta_head omegaBeta

def invalidTop : ParallelStep [[.fn]] (.var 0) (.var 0) :=
  ⟨[],.var 0,⟨.nil _,rfl⟩,rfl⟩
/-- Empty-vertical projection keeps arbitrary actual top programs; validity
of top selection names is deliberately not required. -/
example : ∃ V G, ∃ bottom : ParallelHistory (.var 0) V, ∃ last : ParallelStep G (.var 0) V,
    StepProjection (ParallelStep.empty (.var 0)) (.single invalidTop) bottom last ∧
    ∃eq : V=.var 0,PermEq (eq ▸ bottom) (.single invalidTop) := by
  obtain ⟨V,G,bottom,last,row⟩ := StepProjection.exists_projection (ParallelStep.empty (.var 0)) (.single invalidTop)
  obtain ⟨eq,perm⟩ := row.empty_vertical_permutation (ParallelStep.empty (.var 0))
  cases eq
  exact ⟨.var 0,G,bottom,last,row,rfl,perm⟩

#print axioms StepProjection.permuted_final_selection
#print axioms PermEq.projection_coherence
#print axioms StepProjection.empty_vertical_permutation
#print axioms StepProjection.same_beta_head_permutation
#print axioms PermEq.cancel_beta_head
#print axioms Copy.cancel_beta_head
end Lamping.Checks.PermutationCancellation
