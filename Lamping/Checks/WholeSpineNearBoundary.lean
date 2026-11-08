import Lamping.Lamping.WholeSpineNearBoundary
import Lamping.Checks.SpinePhysicalEvaluation
import Lamping.Checks.UniformOldOuterImageAlignment
namespace Lamping.Checks.WholeSpineNearBoundaryChecks
open Graph Lambda Lambda.Labelled AG
namespace Nested
open UniformOldNodeLabelSuffixChecks
open DirectedMarkerSpineIncidenceChecks.Nested
private def member : {p : Path // p∈[[.fn]]}:=⟨[.fn],by decide⟩

/-- Actual forward schedule; no producer or pair is chosen twice. -/
theorem forward_whole_member_near
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K→Graph.Label signature} {i : Nat}
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V)) {root : B}
    (matching : Matches site.net root sourceWrapped.erase) (inputs : RootInputs site.net root)
    {boundary : B→Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    {endpoint : Marked}
    (relative : Marked.RelativeHistory [[.fn],[.fn]]
      (Marked.mark (site.betaSyntaxFiber root sourceWrapped.erase) sourceWrapped.erase) endpoint)
    (normal : Marked.Normal endpoint)
    (sourceSelection : OccurrenceFragmentSelection sourceWrapped site.net root)
    (targetSelection : OccurrenceFragmentSelection targetForward site.reduce root) :
    INIT originalWrapped ∧History [[.fn],[.fn],[.fn,.arg],[.fn],[.fn]] originalWrapped targetForward ∧
    ∃leaf snapshot,∃geometry : SpineIncidenceProvenance family sourceWrapped (.atom 10) true
      forwardSpine (by rfl : targetForward.subterm [.fn]=some target) leaf snapshot,
      2≤geometry.creationFrames.length ∧leaf.after≠[] ∧
      ∃localTarget,∃localHistory : History [[.fn],[.fn]] (initLabels sourceWrapped.erase) localTarget,
      ∃edge : BetaEdge site.net,
      ∃selection : SourceEdgeSelection (initLabels sourceWrapped.erase) site.net root,
      SiteBetaGeometry site edge ∧
      ∃evaluation : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection (successful_readings.1),
      ∃pair : PairedSpineReannotation geometry localHistory (erase_initLabels sourceWrapped.erase).symm,
      pair.localTailPieces≠[] ∧
      ∃near : SpinePhysicalNearBoundary pair sourceSelection selection edge,
        evaluation.node member=pair.current ∧
        (orientPhysical true (selection.evalLabel edge (evaluation.node member).label)).head?=
          (orientPhysical true ((sourceSelection near.first.position).fragment.segments)).head? := by
  obtain ⟨leaf,snapshot,geometry,multiple,after,_⟩:=PairedMarkerSpineReannotationChecks.Nested.forward_multiple_frames
  obtain ⟨localTarget,localHistory,_erase,_matching,edge,selection,siteGeometry,all⟩:=
    site.beta_evaluated_chain_residuals sourceClosed matching inputs flow positive balance rootDepth transparency
      relative normal labelsForward targetSelection
  obtain ⟨evaluation⟩:=all (successful_readings.1)
  obtain ⟨pair⟩:=geometry.paired_reannotation localHistory (erase_initLabels _).symm
  obtain ⟨near,same,head,_residual,_nonempty⟩:=
    evaluation.given_spine_near_boundary member pair selected matching sourceSelection
  exact ⟨initial,globalPrefix.append labelsForward,leaf,snapshot,geometry,multiple,after,
    localTarget,localHistory,edge,selection,siteGeometry,evaluation,pair,pair.tails_nonempty multiple,
    near,same,head⟩

/-- Actual reverse schedule; no producer or pair is chosen twice. -/
theorem reverse_whole_member_near
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K→Graph.Label signature} {i : Nat}
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V)) {root : B}
    (matching : Matches site.net root sourceWrapped.erase) (inputs : RootInputs site.net root)
    {boundary : B→Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    {endpoint : Marked}
    (relative : Marked.RelativeHistory [[.fn,.arg],[.fn]]
      (Marked.mark (site.betaSyntaxFiber root sourceWrapped.erase) sourceWrapped.erase) endpoint)
    (normal : Marked.Normal endpoint)
    (sourceSelection : OccurrenceFragmentSelection sourceWrapped site.net root)
    (targetSelection : OccurrenceFragmentSelection targetReverse site.reduce root) :
    INIT originalWrapped ∧History [[.fn],[.fn],[.fn,.arg],[.fn,.arg],[.fn]] originalWrapped targetReverse ∧
    ∃leaf snapshot,∃geometry : SpineIncidenceProvenance family sourceWrapped (.atom 10) false
      reverseSpine (by rfl : targetReverse.subterm [.fn]=some reverseResult) leaf snapshot,
      2≤geometry.creationFrames.length ∧leaf.after≠[] ∧
      ∃localTarget,∃localHistory : History [[.fn,.arg],[.fn]] (initLabels sourceWrapped.erase) localTarget,
      ∃edge : BetaEdge site.net,
      ∃selection : SourceEdgeSelection (initLabels sourceWrapped.erase) site.net root,
      SiteBetaGeometry site edge ∧
      ∃evaluation : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection (successful_readings.2),
      ∃pair : PairedSpineReannotation geometry localHistory (erase_initLabels sourceWrapped.erase).symm,
      pair.localTailPieces≠[] ∧
      ∃near : SpinePhysicalNearBoundary pair sourceSelection selection edge,
        evaluation.node member=pair.current ∧
        (orientPhysical false (selection.evalLabel edge (evaluation.node member).label)).head?=
          (orientPhysical false ((sourceSelection near.first.position).fragment.segments)).head? := by
  obtain ⟨leaf,snapshot,geometry,multiple,after,_⟩:=PairedMarkerSpineReannotationChecks.Nested.reverse_multiple_frames
  obtain ⟨localTarget,localHistory,_erase,_matching,edge,selection,siteGeometry,all⟩:=
    site.beta_evaluated_chain_residuals sourceClosed matching inputs flow positive balance rootDepth transparency
      relative normal labelsReverse targetSelection
  obtain ⟨evaluation⟩:=all (successful_readings.2)
  obtain ⟨pair⟩:=geometry.paired_reannotation localHistory (erase_initLabels _).symm
  obtain ⟨near,same,head,_residual,_nonempty⟩:=
    evaluation.given_spine_near_boundary member pair selected matching sourceSelection
  exact ⟨initial,globalPrefix.append labelsReverse,leaf,snapshot,geometry,multiple,after,
    localTarget,localHistory,edge,selection,siteGeometry,evaluation,pair,pair.tails_nonempty multiple,
    near,same,head⟩
end Nested
namespace MarkedLast
open UniformOldOuterImageAlignmentChecks.MarkedLast

theorem currentMarked : ¬current.label.OuterBarsSafe (fun d=>d≠Label.atom 10) := by
  intro safe
  change (Label.atom 10≠Label.atom 10) ∧_ at safe
  exact safe.1 rfl

def actualSpine : DirectedMarkerSpine F source (.atom 10) true [[.arg],[]] target [] [.fn]:=
  old.directed_marker_spine labels selected sourceSafe .refl reading rfl currentMarked (by simp)

/-- Separate compound marked-LAST case: the genuine two-edge whole chain
and five-key local node identify the exact source FIRST occurrence. -/
theorem actual_marked_last_near_atom :
    INIT original ∧History [[],[],[.arg],[.arg],[]] original target ∧
    PrerequisiteChain target [] [[.fn],[.fn,.fn]] ∧
    ¬lastNode.label.OuterBarsSafe (fun d=>d≠Label.atom 10) ∧¬IsAtomic oldBeta ∧
    ∃leaf snapshot,
    ∃geometry : SpineIncidenceProvenance F source (.atom 10) true actualSpine
      (by rfl : target.subterm [.fn]=some current) leaf snapshot,
    ∃pair : PairedSpineReannotation geometry localLabels (erase_initLabels source.erase).symm,
    ∃first : SpineNearFirstAtom pair,
      first.atom=3 ∧first.position.val=[.fn,.body,.fn] ∧
      source.subterm first.position.val=some (.var (.atom 12) 0) ∧
      pair.current=localCurrent ∧
      pair.current.label.letters=[.atom 3,.under (.atom 1),.atom 5,.over (.atom 6),.atom 7] := by
  obtain ⟨leaf,snapshot,⟨geometry⟩⟩:=actualSpine.incidence_leaf_output (globalPrefix.closed originalClosed)
    (by rfl : target.subterm [.fn]=some current)
  obtain ⟨pair⟩:=geometry.paired_reannotation localLabels (erase_initLabels _).symm
  obtain ⟨first⟩:=Lamping.AG.PairedSpineReannotation.near_first_atom pair selected
  have currentEq : pair.current=localCurrent:=Option.some.inj (pair.currentLookup.symm.trans (by rfl))
  have atomEq : first.atom=3 := by
    have head:=congrArg List.head? first.word
    rw [currentEq] at head
    change some (Letter.atom 3)=some (.atom first.atom) at head
    exact (Letter.atom.inj (Option.some.inj head)).symm
  have positionEq : first.position.val=[.fn,.body,.fn] :=
    LTerm.subterm_label_injective (initLabels source.erase) (init_is_INIT _).2 first.basisLookup
      (by rfl : localSource.subterm [.fn,.body,.fn]=some (.var (.atom 3) 0))
      (by rw [first.basisAtomic,atomEq];rfl)
  exact ⟨initial,globalPrefix.append labels,chain,lastMarked,oldBetaCompound,leaf,snapshot,
    geometry,pair,first,atomEq,positionEq,by rw [positionEq];rfl,currentEq,by rw [currentEq];rfl⟩
end MarkedLast

#print axioms Lamping.AG.PairedSpineReannotation.near_first_atom
#print axioms Lamping.AG.PairedSpineReannotation.physical_near_boundary
#print axioms EvaluatedChainResiduals.given_spine_near_boundary
#print axioms Nested.forward_whole_member_near
#print axioms Nested.reverse_whole_member_near
#print axioms MarkedLast.currentMarked
#print axioms MarkedLast.actual_marked_last_near_atom
end Lamping.Checks.WholeSpineNearBoundaryChecks
