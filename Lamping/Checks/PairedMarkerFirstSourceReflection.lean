import Lamping.Lamping.PairedMarkerFirstSourceReflection
import Lamping.Checks.PairedMarkerFirstComparison

namespace Lamping.Checks.PairedMarkerFirstSourceReflectionChecks
open Graph Lambda Lambda.Labelled AG

namespace InitialPhysical
open BetaBeforeBlockImagesChecks

/-- The existing actual INIT physical producer supplies its real selection,
edge, two event reannotations and honest initial Joint. The NEW reflection
is called on those SAME objects; no distinct physical comparison is asserted. -/
theorem actual_initial_joint_source_reflection
    (targetSelection : OccurrenceFragmentSelection target site.reduce (.inl ())) :
    ∃ sourceSelection : OccurrenceFragmentSelection source site.net (.inl ()),
      JointRepresentation WrappedSuccessfulChains.sourceClosed sourceSelection ∧
      ∃ localTarget,History [[.fn]] (initLabels source.erase) localTarget ∧
        ∃ edge : BetaEdge site.net,∃ selection : SourceEdgeSelection (initLabels source.erase) site.net (.inl ()),
          ∃ leaf : DirectedMarkerLeafOutput [[.fn]] source (.atom 2) true [[.fn]] functionTerm.label.letters,
            ∃ lp rp : PairedMarkerEventGeometry leaf (initLabels source.erase) localTarget,
              selection.evalLabel edge lp.firstNode.label=selection.evalLabel edge rp.firstNode.label ∧
              leaf.firstNode.label=leaf.firstNode.label := by
  obtain ⟨sourceSelection,joint,localTarget,localHistory,edge,selection,leaf,lp,rp,same⟩ :=
    PairedMarkerFirstComparisonChecks.InitialPhysical.actual_initial_joint_comparison targetSelection
  have originalMatches : Matches FunctionWrappedReachable.net (.inl ()) source.erase :=
    encode_closed_matches FunctionWrappedReachable.term FunctionWrappedReachable.closed 0
  have matching := FunctionWrappedReachable.concrete.sourceIso.matches originalMatches
  have reflected := paired_marker_first_source_labels_of_evaluations leaf leaf lp rp matching selected
    (WrappedSuccessfulChains.initial.outerBarsSafe _) (.nil source) WrappedSuccessfulChains.initial
    WrappedSuccessfulChains.sourceClosed sourceSelection joint.1 selection edge same
  exact ⟨sourceSelection,joint,localTarget,localHistory,edge,selection,leaf,lp,rp,same,reflected⟩
end InitialPhysical

namespace Noninitial
open UniformOldCreatedIncomingLabelsChecks.Distinct MarkerLeafSourceFirstChainsChecks
private theorem sourceClosed : Closed source.erase :=
  globalHistory.closed actual_same_initial_two_old.2.1

/-- Genuine distinct source coordinates and original INIT history remain
visible. SOURCE REP is explicitly conditional, never asserted graph truth. -/
theorem actual_distinct_conditional_source_reflection
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (representation : ChainRepresentationInvariant sourceClosed sourceSelection)
    (selection : SourceEdgeSelection (initLabels source.erase) g root) (physical : BetaEdge g) :
    ¬INIT source ∧oldLeft≠oldRight ∧
      ∃ localTarget,History [left,right] (initLabels source.erase) localTarget ∧
        ∃ lp : PairedMarkerEventGeometry leftLeaf (initLabels source.erase) localTarget,
          ∃ rp : PairedMarkerEventGeometry rightLeaf (initLabels source.erase) localTarget,
            selection.evalLabel physical lp.firstNode.label=selection.evalLabel physical rp.firstNode.label ∧
              leftLeaf.firstNode.label=rightLeaf.firstNode.label := by
  obtain ⟨notInitial,distinct,localTarget,localHistory,lp,rp,same⟩ :=
    PairedMarkerFirstComparisonChecks.Noninitial.actual_distinct_first_comparison
      matching sourceSelection representation selection physical
  have reflected := paired_marker_first_source_labels_of_evaluations leftLeaf rightLeaf lp rp matching
    selected source_safe globalHistory initial sourceClosed sourceSelection representation selection physical same
  exact ⟨notInitial,distinct,localTarget,localHistory,lp,rp,same,reflected⟩
end Noninitial

#print axioms InitialPhysical.actual_initial_joint_source_reflection
#print axioms Noninitial.actual_distinct_conditional_source_reflection
end Lamping.Checks.PairedMarkerFirstSourceReflectionChecks
