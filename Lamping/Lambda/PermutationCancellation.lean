import Lamping.Lambda.ProjectionPermutation
import Lamping.Lambda.InitialFamilies
import Lamping.Lambda.ProjectionStepCongruence
namespace Lamping.Lambda

/-- An actually empty vertical row projects its top history to the same
permutation class, including invalid or repeated names in the top steps. -/
theorem StepProjection.empty_vertical_permutation (h : ParallelStep [] t t)
    {σ : ParallelHistory t v} {bottom : ParallelHistory t w} {last : ParallelStep G v w}
    (row : StepProjection h σ bottom last) :
    ∃eq : w=v,PermEq (eq ▸ bottom) σ := by
  have valid : ∀p∈([] : List Path),∃z,subtermAt t p=some z ∧ IsRedex z := by intro p hp; cases hp
  have finalEmpty : G=[] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro p hp
    let s : RedexOcc v := ⟨p,row.final_selection_valid valid p hp⟩
    obtain ⟨r,hr,_⟩ := (row.final_selection valid s).mp hp
    cases hr
  subst G
  have endpoint : w=v := last.endpoint_selection (ParallelStep.empty v) (fun _ => Iff.rfl)
  cases endpoint
  refine ⟨rfl,?_⟩
  have left : PermEq ((ParallelHistory.single h).append bottom) bottom := by
    simpa only [ParallelHistory.append] using PermEq.comp (PermEq.empty h) (PermEq.refl bottom)
  have right : PermEq (σ.append (.single last)) σ := by
    simpa only [ParallelHistory.append_nil] using PermEq.comp (PermEq.refl σ) (PermEq.empty last)
  exact left.symm.trans (row.permutation.trans right)

private theorem uncons_row (h : ParallelStep H t U) (head : ParallelStep F t A)
    (tail : ParallelHistory A B) {bottom : ParallelHistory U V} {last : ParallelStep K B V}
    (row : StepProjection h (.cons head tail) bottom last) :
    ∃ M, ∃ first : ParallelStep (h.residualSet F) U M,
      ∃ vertical : ParallelStep (head.residualSet H) A M,
      ∃ rest : ParallelHistory M V, StepProjection vertical tail rest last ∧ bottom=.cons first rest := by
  cases row with | cons square remaining => exact ⟨_,square.afterFirst,square.afterSecond,_,remaining,rfl⟩

/-- Projecting a history through its own actual first beta deletes that
head, up to generated permutation of the given projected schedule. -/
theorem StepProjection.same_beta_head_permutation (R : BetaAt m p t)
    (tail : ParallelHistory t u) {bottom : ParallelHistory t w} {last : ParallelStep G u w}
    (row : StepProjection (singleContraction R)
      ((ParallelHistory.single (singleContraction R)).append tail) bottom last) :
    ∃eq : w=u,PermEq (eq ▸ bottom) tail := by
  obtain ⟨M,first,vertical,rest,remaining,bottomEq⟩ := uncons_row (singleContraction R) (singleContraction R) tail row
  have names : (singleContraction R).residualSet [p]=[] :=
    (singleContraction R).residualSet_empty_of_equiv (fun _ => Iff.rfl)
  have middle : M=t := first.endpoint_selection (ParallelStep.empty t) (by intro q; rw [names])
  cases middle
  let firstEmpty : ParallelStep [] t t := names ▸ first
  let verticalEmpty : ParallelStep [] t t := names ▸ vertical
  have remainingEmpty : StepProjection verticalEmpty tail rest last := by
    exact remaining.first_congr names (ParallelStep.paths_cast names vertical).symm
  obtain ⟨endpoint,tailPerm⟩ := remainingEmpty.empty_vertical_permutation verticalEmpty
  cases endpoint
  refine ⟨rfl,?_⟩
  have firstPerm : PermEq (.single first) (.nil t) := by
    have castSame : ParallelHistory.single firstEmpty=ParallelHistory.single first := by
      exact ParallelHistory.cons_selection_cast names first (.nil t)
    rw [←castSame]
    exact .empty firstEmpty
  rw [bottomEq]
  have removeFirst : PermEq (.cons first rest) rest := by
    simpa only [ParallelHistory.single,ParallelHistory.append] using PermEq.comp firstPerm (PermEq.refl rest)
  exact removeFirst.trans tailPerm

/-- Left cancellation of the same actual singleton beta, proved by
projecting both genuinely permutation-equivalent programs through that beta.
No confluence, family uniqueness or Copy-to-join premise is used. -/
theorem PermEq.cancel_beta_head (R : BetaAt m p t) {a b : ParallelHistory t u}
    (perm : PermEq ((ParallelHistory.single (singleContraction R)).append a)
      ((ParallelHistory.single (singleContraction R)).append b)) : PermEq a b := by
  obtain ⟨A,F,left,lastLeft,rowLeft⟩ := StepProjection.exists_projection (singleContraction R)
    ((ParallelHistory.single (singleContraction R)).append a)
  obtain ⟨B,G,right,lastRight,rowRight⟩ := StepProjection.exists_projection (singleContraction R)
    ((ParallelHistory.single (singleContraction R)).append b)
  obtain ⟨endLeft,leftPerm⟩ := rowLeft.same_beta_head_permutation R a
  cases endLeft
  obtain ⟨endRight,rightPerm⟩ := rowRight.same_beta_head_permutation R b
  cases endRight
  obtain ⟨endpoint,projectedPerm⟩ := perm.projection_coherence (singleContraction R) (singleContraction R)
    (fun _ => Iff.rfl) (by intro q hq; cases List.mem_singleton.mp hq; exact R.redex) rowLeft rowRight
  exact leftPerm.symm.trans (projectedPerm.trans rightPerm)

theorem Copy.cancel_beta_head (R : BetaAt m p t) (a b : RedexWithHistory t)
    (copy : Copy ⟨a.target,(ParallelHistory.single (singleContraction R)).append a.history,a.redex⟩
      ⟨b.target,(ParallelHistory.single (singleContraction R)).append b.history,b.redex⟩) : Copy a b := by
  obtain ⟨extension,perm,residual⟩ := copy
  refine ⟨extension,?_,residual⟩
  rw [ParallelHistory.append_assoc] at perm
  exact perm.cancel_beta_head R

end Lamping.Lambda
