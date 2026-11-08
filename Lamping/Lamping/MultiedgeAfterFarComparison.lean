import Lamping.Lamping.GivenParentCanonicalFarComparison
namespace Lamping.AG
open Graph Lambda Lambda.Labelled SyntaxIncidence

theorem canonical_multiedge_after_far_comparison
    {initialSource source current : LTerm} {prior ps F : List Path}
    {degree : Label} {endpoint : Marked}
    {leftStart rightStart : Path} {leftEdges rightEdges : List Path}
    (initial : INIT initialSource) (prefixHistory : History prior initialSource source)
    (sourceClosed : Closed source.erase)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) endpoint)
    (labels : History ps source current)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (leftCut : ActualUnsafeMarkerCut F ps source current degree leftStart leftEdges)
    (rightCut : ActualUnsafeMarkerCut F ps source current degree rightStart rightEdges)
    (leftSnapshot : IncomingIncidenceSnapshot current leftCut.edge)
    (rightSnapshot : IncomingIncidenceSnapshot current rightCut.edge)
    (left : CanonicalAfterFarOutput labels leftCut leftSnapshot)
    (right : CanonicalAfterFarOutput labels rightCut rightSnapshot)
    (afterIso : ChainIncidenceIso
      (chainSyntaxIncidence current (labels.closed sourceClosed) leftCut.after)
      (chainSyntaxIncidence current (labels.closed sourceClosed) rightCut.after))
    (multipleAfter : 1<leftCut.after.length) :
    CanonicalFarFullComparison sourceClosed left right := by
  have leftMore := left.currentChain.nonempty
  have rightMore := right.currentChain.nonempty
  obtain ⟨l,r,result⟩ := canonical_after_far_comparison initial prefixHistory sourceClosed old labels
    selected sourceSafe leftCut rightCut leftMore rightMore leftSnapshot rightSnapshot afterIso
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
      have signs := SignedProperWalk.signs_eq_of_multiedge full initial l.currentChain r.currentChain
        lwalk rwalk afterLabels multipleAfter
      obtain ⟨_av,_ap,_ai,asign⟩ := a.signed_slot lwalk (Or.inl rfl)
      obtain ⟨_bv,_bp,_bi,bsign⟩ := b.signed_slot rwalk (Or.inl rfl)
      have ordinal : a.before.length=b.before.length := by
        simpa only [List.length_map] using congrArg List.length beforeEq
      have signEq : a.forward=b.forward := by
        rw [signs,ordinal] at asign
        exact Option.some.inj (asign.symm.trans bsign)
      exact False.elim (opposed signEq)
  obtain ⟨_lcurrent,_lsource,le⟩ := l.source_data_unique left
  obtain ⟨_rcurrent,_rsource,re⟩ := r.source_data_unique right
  simpa only [CanonicalFarFullComparison,le,re] using good

#print axioms canonical_multiedge_after_far_comparison

end Lamping.AG
