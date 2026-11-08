import Lamping.Lambda.StandardizationNoReturn
import Lamping.Lambda.OrdinarySplits
import Lamping.Lambda.ProjectionSelections
namespace Lamping.Lambda
/-- An old redex actually contracted by an ordinary internal history must
itself originate in that subtree; outside old names remain at their paths. -/
theorem UsedSource.internal {ρ : ParallelHistory t u} {r : RedexOcc t}
    (used : UsedSource ρ r) (atomic : Atomic ρ) (inside : Internal site ρ) :
    ∃ q, r.val=site++q := by
  classical
  apply Classical.byContradiction
  intro outside
  obtain ⟨v,w,F,pre,step,suffix,q,eq,selected,residual⟩ := used
  have prefixInside : Internal site pre := by
    intro p hp
    exact inside p (by rw [eq,ParallelHistory.derivation_append]; change p∈pre.derivation.paths++_; exact List.mem_append_left _ hp)
  have whole : Atomic (pre.append (.cons step suffix)) := by rw [←eq]; exact atomic
  have rest := whole.split_append.2
  cases rest with
  | cons head tail =>
    have same : q.val=_ := List.mem_singleton.mp selected
    have selectedInside : ∃ s, q.val=site++s := inside q.val (by
      rw [eq,ParallelHistory.derivation_append]
      change q.val∈pre.derivation.paths++(_::_)
      exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl same)))
    have fixed := (pre.residual_outside_internal prefixInside r q outside).mp residual
    exact outside (by rw [fixed]; exact selectedInside)

private theorem projection_uncons {first : ParallelStep F t u} {top : ParallelStep H t v}
    {rest : ParallelHistory v x} {full : ParallelHistory u z} {last : ParallelStep G x z}
    (row : StepProjection first (.cons top rest) full last) :
    ∃ (mid : Term) (tail : ParallelHistory mid z) (sq : ParallelMovesSquare F H t u v mid),
      sq.first=first ∧ sq.second=top ∧ full=.cons sq.afterFirst tail ∧
      StepProjection sq.afterSecond rest tail last := by
  cases row with | cons sq tail => exact ⟨_,_,sq,rfl,rfl,rfl,tail⟩

/-- Actual selection of an old source redex projects to selection of its
unique original image. The witness is built from the given row schedules. -/
theorem UsedSource.project_unique {ρ : ParallelHistory t v} {τ : ParallelHistory u w}
    {vertical : ParallelStep F t u} {last : ParallelStep G v w}
    (row : StepProjection vertical ρ τ last) (sourceAtomic : Atomic ρ) (targetAtomic : Atomic τ)
    (r : RedexOcc t) (image : RedexOcc u)
    (unique : ∀ q : RedexOcc u, vertical.derivation.Residual r q → q=image)
    (used : UsedSource ρ r) : UsedSource τ image := by
  obtain ⟨a,b,H,pre,step,suffix,q,eq,selected,residual⟩ := used
  have whole : Atomic (pre.append (.cons step suffix)) := by rw [←eq]; exact sourceAtomic
  have rest := whole.split_append.2
  cases rest with
  | cons head restAtomic =>
    have qSame : q=⟨_,head.redex⟩ := Subtype.ext (List.mem_singleton.mp selected)
    subst q
    rw [eq] at row
    obtain ⟨mid,K,bottomPre,mapped,atPre,preRow,restRow,fullEq⟩ := row.split_append pre (.cons (singleContraction head) suffix)
    have bottomRestAtomic : Atomic mapped := (fullEq ▸ targetAtomic).split_append.2
    obtain ⟨next,bottomTail,square,firstEq,secondEq,mappedEq,tailRow⟩ := projection_uncons restRow
    rcases square with ⟨firstVertical,firstTop,projected,afterTop⟩
    simp only at firstEq secondEq mappedEq tailRow
    subst firstVertical
    subst firstTop
    have projectedAtomic : Atomic (.single projected) := by
      rw [mappedEq] at bottomRestAtomic
      exact (bottomRestAtomic.split_append (ρ:=.single projected) (σ:=bottomTail)).1
    obtain ⟨p,beta,paths⟩ := projectedAtomic.single_step
    let target : RedexOcc mid := ⟨p,beta.redex⟩
    have verticalResidual : atPre.derivation.Residual ⟨_,head.redex⟩ target :=
      atPre.singleton_projection_residual ⟨_,head.redex⟩ target projected paths
    have topComposite : (pre.append (.single atPre)).derivation.Residual r target := by
      rw [ParallelHistory.derivation_append,ParallelHistory.single_derivation,Derivation.residual_append]
      exact ⟨⟨_,head.redex⟩,residual,verticalResidual⟩
    have bottomComposite := (preRow.permutation.residual r target).mpr topComposite
    rw [ParallelHistory.derivation_append,ParallelHistory.single_derivation,Derivation.residual_append] at bottomComposite
    obtain ⟨old,first,lastResidual⟩ := bottomComposite
    have same := unique old first
    subst old
    refine ⟨mid,next,_,bottomPre,projected,bottomTail,target,?_,?_,lastResidual⟩
    · rw [fullEq,mappedEq]
    · exact projected.first_selected paths
end Lamping.Lambda
