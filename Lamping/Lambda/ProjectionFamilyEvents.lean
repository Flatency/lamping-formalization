import Lamping.Lambda.FamilyDevelopments
import Lamping.Lambda.ProjectionFamilies
namespace Lamping.Lambda

theorem Atomic.head_data {h : ParallelStep F t v} {tail : ParallelHistory v w}
    (ha : Atomic (.cons h tail)) :
    ∃ p, ∃ _R : BetaAt t p v, F=[p] ∧ h.paths=[p] ∧ Atomic tail := by
  cases ha with
  | cons R rest => exact ⟨_,R,rfl,rfl,rest⟩

/-- Ordinary horizontal projections transport every actual selected family
event. This is directional support, not invariance under permutation. -/
theorem StepProjection.family_used_forward
    {step : ParallelStep F t u} {top : ParallelHistory t v}
    {bottom : ParallelHistory u w} {last : ParallelStep G v w}
    (row : StepProjection step top bottom last) (ht : Atomic top) (hb : Atomic bottom)
    (pre : ParallelHistory m t) (used : FamilyUsedAt pre top a) :
    FamilyUsedAt (pre.append (.single step)) bottom a := by
  induction row generalizing m a with
  | nil => cases used
  | cons sq row ih =>
    obtain ⟨p,R,selection,_,htail⟩ := ht.head_data
    obtain ⟨q,S,bselection,paths,btail⟩ := hb.head_data
    cases used with
    | head selected family =>
      rw [selection] at selected
      have ep := List.mem_singleton.mp selected
      have er : _ = (⟨p,R.redex⟩ : RedexOcc _) := Subtype.ext ep
      subst er
      have selectedq := sq.afterFirst.first_selected paths
      change q ∈ sq.first.residualSet _ at selectedq
      have selectedq' : q ∈ sq.first.residualSet [p] :=
        (congrArg (fun names => q ∈ sq.first.residualSet names) selection).mp selectedq
      obtain ⟨r,hr,trace⟩ := (Marked.mem_setResidualPositions [p] sq.first.markedTarget q).mp selectedq'
      have eq := List.mem_singleton.mp hr
      subst r
      have old := (sq.first.residual_iff ⟨p,R.redex⟩ ⟨q,S.redex⟩).mpr trace
      have copy : Copy ⟨_,pre,⟨p,R.redex⟩⟩
          ⟨_,pre.append (.single sq.first),⟨q,S.redex⟩⟩ :=
        ⟨.single sq.first,.refl _,by simpa only [ParallelHistory.single_derivation] using old⟩
      exact .head (by rw [bselection]; simp)
        (.trans (.symm (.copy copy)) family)
    | tail used =>
      apply FamilyUsedAt.tail
      have moved := ih htail btail (pre.append (.single sq.second)) used
      apply moved.prefix_permutation
      simpa only [ParallelHistory.append_assoc] using
        (PermEq.prepend pre (PermEq.moves sq)).symm

end Lamping.Lambda
