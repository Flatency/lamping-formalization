import Lamping.Lambda.PermutationCancellation
import Lamping.Lambda.StandardizationProtection
namespace Lamping.Lambda

/-- The initial old head has no residual after its actual contraction,
so every actual row projecting that headed history has empty last selection. -/
theorem StepProjection.self_beta_head_last_empty (R : BetaAt m p t)
    (tail : ParallelHistory t u) {bottom : ParallelHistory t w} {last : ParallelStep G u w}
    (row : StepProjection (singleContraction R)
      ((ParallelHistory.single (singleContraction R)).append tail) bottom last) : G=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro q hq
  have valid : ∀r∈[p],∃z,subtermAt m r=some z ∧ IsRedex z := by
    intro r hr; cases List.mem_singleton.mp hr; exact R.redex
  let target : RedexOcc u := ⟨q,row.final_selection_valid valid q hq⟩
  obtain ⟨old,selected,residual⟩ := (row.final_selection valid target).mp hq
  have oldSame : old=⟨p,R.redex⟩ := Subtype.ext (List.mem_singleton.mp selected)
  subst old
  rw [ParallelHistory.derivation_append,ParallelHistory.single_derivation,Derivation.residual_append] at residual
  obtain ⟨middle,first,_⟩ := residual
  exact (singleContraction R).no_selected_residual ⟨p,R.redex⟩ (by simp) middle first

/-- Project a Copy relation through the target's actual first beta. A
particular source image is recovered from the real extension rectangle;
the statement deliberately does not quantify over all duplicated images. -/
theorem Copy.project_target_head (R : BetaAt m p t) (a : RedexWithHistory m) (b : RedexWithHistory t)
    (copy : Copy a ⟨b.target,(ParallelHistory.single (singleContraction R)).append b.history,b.redex⟩)
    {prefix' : ParallelHistory t A} {vertical : ParallelStep F a.target A}
    (row : StepProjection (singleContraction R) a.history prefix' vertical) :
    ∃ image : RedexOcc A, vertical.derivation.Residual a.redex image ∧
      Copy ⟨A,prefix',image⟩ b := by
  obtain ⟨extension,perm,residual⟩ := copy
  obtain ⟨B,G,extension',last,rowExtension⟩ := StepProjection.exists_projection vertical extension
  have totalRow := row.append rowExtension
  obtain ⟨C,H,target',lastTarget,targetRow⟩ := StepProjection.exists_projection (singleContraction R)
    ((ParallelHistory.single (singleContraction R)).append b.history)
  obtain ⟨targetEnd,targetPerm⟩ := targetRow.same_beta_head_permutation R b.history
  cases targetEnd
  have valid : ∀r∈[p],∃z,subtermAt m r=some z ∧ IsRedex z := by
    intro r hr; cases List.mem_singleton.mp hr; exact R.redex
  obtain ⟨endpoint,projectedPerm⟩ := perm.projection_coherence (singleContraction R) (singleContraction R)
    (fun _ => Iff.rfl) valid totalRow targetRow
  cases endpoint
  have targetEmpty : H=[] := targetRow.self_beta_head_last_empty R b.history
  have lastNames := StepProjection.permuted_final_selection perm (singleContraction R) (singleContraction R)
    (fun _ => Iff.rfl) valid totalRow targetRow
  have lastEmpty : G=[] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro q hq
    have h := (lastNames q).mp hq
    rw [targetEmpty] at h
    cases h
  subst G
  have lastResidual : last.derivation.Residual b.redex b.redex := by
    have same := last.residual_independent (ParallelStep.empty b.target) b.redex b.redex
    apply same.mpr
    exact (Derivation.residual_nil b.redex b.redex).mpr rfl
  have composite : (extension.append (.single last)).derivation.Residual a.redex b.redex := by
    rw [ParallelHistory.derivation_append,ParallelHistory.single_derivation,Derivation.residual_append]
    exact ⟨b.redex,residual,lastResidual⟩
  have transported := (rowExtension.permutation.residual a.redex b.redex).mpr composite
  rw [ParallelHistory.derivation_append,ParallelHistory.single_derivation,Derivation.residual_append] at transported
  obtain ⟨image,oldImage,extensionResidual⟩ := transported
  exact ⟨image,oldImage,extension',projectedPerm.trans targetPerm,extensionResidual⟩

end Lamping.Lambda
