import Lamping.Lamping.PhysicalReadingRoles
import Lamping.Lamping.GivenParentCanonicalFarComparison
namespace Lamping.AG
open Graph Lambda Lambda.Labelled SyntaxIncidence
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}
theorem actual_physical_after_far_comparison
    {initialSource source current : LTerm} {prior ps F : List Path}
    {degree : Label} {endpoint : Marked}
    {leftStart rightStart : Path} {leftEdges rightEdges : List Path}
    (initial : INIT initialSource) (prefixHistory : History prior initialSource source)
    (sourceClosed : Closed source.erase)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) endpoint)
    (labels : History ps source current)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (matching : Matches g root current.erase)
    (selection : OccurrenceFragmentSelection current g root)
    (leftParent : PrerequisiteChain current leftStart leftEdges)
    (rightParent : PrerequisiteChain current rightStart rightEdges)
    (physical : SameChainRepresentation selection leftParent rightParent)
    (leftCut : ActualUnsafeMarkerCut F ps source current degree leftStart leftEdges)
    (rightCut : ActualUnsafeMarkerCut F ps source current degree rightStart rightEdges)
    (sameBefore : leftCut.before.length=rightCut.before.length)
    (leftSnapshot : IncomingIncidenceSnapshot current leftCut.edge)
    (rightSnapshot : IncomingIncidenceSnapshot current rightCut.edge)
    (left : CanonicalAfterFarOutput labels leftCut leftSnapshot)
    (right : CanonicalAfterFarOutput labels rightCut rightSnapshot)
    (afterIso : ChainIncidenceIso
      (chainSyntaxIncidence current (labels.closed sourceClosed) leftCut.after)
      (chainSyntaxIncidence current (labels.closed sourceClosed) rightCut.after)) :
    CanonicalFarFullComparison sourceClosed left right := by
  have leftMore := left.currentChain.nonempty
  have rightMore := right.currentChain.nonempty
  obtain ⟨_rightMore,_direction,ls0,rs0,l0,r0,kind,lk,rk⟩ :=
    actual_parent_cut_physical_reading_roles matching sourceClosed labels selection
      leftParent rightParent physical leftCut rightCut sameBefore leftMore
  have lse := ls0.unique leftSnapshot
  have rse := rs0.unique rightSnapshot
  subst ls0;subst rs0
  obtain ⟨l0current,_l0source,_l0edges⟩ := l0.source_data_unique left
  obtain ⟨r0current,_r0source,_r0edges⟩ := r0.source_data_unique right
  have givenKind : ∃k,ProperKind current left.currentProper k ∧
      ProperKind current right.currentProper k := by
    exact ⟨kind,l0current ▸ lk,r0current ▸ rk⟩
  obtain ⟨l,r,result⟩ := canonical_after_far_comparison initial prefixHistory sourceClosed old labels
    selected sourceSafe leftCut rightCut leftMore rightMore leftSnapshot rightSnapshot afterIso
  obtain ⟨lcurrent,_lsource,le⟩ := l.source_data_unique left
  obtain ⟨rcurrent,_rsource,re⟩ := r.source_data_unique right
  have actualKind : ∃k,ProperKind current l.currentProper k ∧
      ProperKind current r.currentProper k := by
    obtain ⟨k,kl,kr⟩ := givenKind
    exact ⟨k,lcurrent.symm ▸ kl,rcurrent.symm ▸ kr⟩
  have good : CanonicalFarFullComparison sourceClosed l r := by
    rcases result with safe | same | opposite
    · exact safe.2
    · obtain ⟨_lc,_rc,_sign,_front,_head,comparison⟩ := same
      exact comparison
    · obtain ⟨a,b,_terminalLeft,_terminalRight,opposed,beforeEq,_head⟩ := opposite
      obtain ⟨lf,ss,vs,lt,lwalk⟩ := l.currentChain.signed_path
      obtain ⟨rf,ts,ws,rt,rwalk⟩ := r.currentChain.signed_path
      have lfEq : lf=l.currentProper := Option.some.inj (Target.unique lt (Or.inl rfl))
      have rfEq : rf=r.currentProper := Option.some.inj (Target.unique rt (Or.inl rfl))
      subst lf;subst rf
      have full := prefixHistory.append labels
      have afterLabels := actual_chain_labels_forward full initial (labels.closed sourceClosed)
        l.currentChain r.currentChain afterIso
      have signs := SignedProperWalk.signs_eq full initial lwalk rwalk afterLabels actualKind
      obtain ⟨_av,_ap,_ai,asign⟩ := a.signed_slot lwalk (Or.inl rfl)
      obtain ⟨_bv,_bp,_bi,bsign⟩ := b.signed_slot rwalk (Or.inl rfl)
      have ordinal : a.before.length=b.before.length := by
        simpa only [List.length_map] using congrArg List.length beforeEq
      have signEq : a.forward=b.forward := by
        rw [signs,ordinal] at asign
        exact Option.some.inj (asign.symm.trans bsign)
      exact False.elim (opposed signEq)
  simpa only [CanonicalFarFullComparison,le,re] using good

#print axioms actual_physical_after_far_comparison
end
end Lamping.AG
