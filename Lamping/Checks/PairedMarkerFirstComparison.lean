import Lamping.Lamping.PairedMarkerFirstComparison
import Lamping.Checks.MarkerLeafSourceFirstChains
import Lamping.Checks.PairedMarkerLeafGeometry
import Lamping.Lamping.InitialJointRepresentation
import Lamping.Lamping.JointRepresentationTransport
namespace Lamping.Checks.PairedMarkerFirstComparisonChecks
open Graph Lambda Lambda.Labelled AG

namespace Noninitial
open UniformOldCreatedIncomingLabelsChecks.Distinct MarkerLeafSourceFirstChainsChecks
private theorem sourceClosed : Closed source.erase :=
  globalHistory.closed actual_same_initial_two_old.2.1

/-- Real distinct-leaf nonINIT data and its actual original INIT prefix.
The physical SOURCE REP is an explicit induction hypothesis; this does not
assert its truth at an actual nonINIT physical graph. -/
theorem actual_distinct_first_comparison
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
            selection.evalLabel physical lp.firstNode.label=selection.evalLabel physical rp.firstNode.label := by
  obtain ⟨localTarget,localHistory,_erase⟩ := lift_history labels.betaHistory (initLabels source.erase) (erase_initLabels source.erase)
  obtain ⟨lp⟩ := paired_marker_leaf_geometry leftLeaf localHistory (erase_initLabels source.erase).symm
  obtain ⟨rp⟩ := paired_marker_leaf_geometry rightLeaf localHistory (erase_initLabels source.erase).symm
  have same := paired_marker_first_evaluations leftLeaf rightLeaf lp rp matching selected source_safe
    globalHistory initial sourceClosed sourceSelection representation selection physical rfl
  exact ⟨actual_source_is_noninitial,by decide,localTarget,localHistory,lp,rp,same⟩
end Noninitial

namespace InitialPhysical
open BetaBeforeBlockImagesChecks

/-- Actual initial Joint truth is supplied by the initial theorem and the
real source isomorphism. The SAME producer exposes a marked child; this
integration consumer compares that one leaf with itself, not distinct READs. -/
theorem actual_initial_joint_comparison
    (targetSelection : OccurrenceFragmentSelection target site.reduce (.inl ())) :
    ∃ sourceSelection : OccurrenceFragmentSelection source site.net (.inl ()),
      JointRepresentation WrappedSuccessfulChains.sourceClosed sourceSelection ∧
      ∃ localTarget,History [[.fn]] (initLabels source.erase) localTarget ∧
        ∃ edge : BetaEdge site.net,∃ selection : SourceEdgeSelection (initLabels source.erase) site.net (.inl ()),
          ∃ leaf : DirectedMarkerLeafOutput [[.fn]] source (.atom 2) true [[.fn]] functionTerm.label.letters,
            ∃ lp rp : PairedMarkerEventGeometry leaf (initLabels source.erase) localTarget,
              selection.evalLabel edge lp.firstNode.label=selection.evalLabel edge rp.firstNode.label := by
  have originalMatches : Matches FunctionWrappedReachable.net (.inl ()) source.erase :=
    encode_closed_matches FunctionWrappedReachable.term FunctionWrappedReachable.closed 0
  have matching := FunctionWrappedReachable.concrete.sourceIso.matches originalMatches
  obtain ⟨initialSelection,initialJoint⟩ := encode_initial_joint_realization source
    WrappedSuccessfulChains.sourceClosed WrappedSuccessfulChains.initial 0
  obtain ⟨sourceSelection⟩ := matching.occurrence_fragment_selection WrappedSuccessfulChains.sourceClosed
  have joint := (FunctionWrappedReachable.concrete.sourceIso.joint_representation originalMatches
    WrappedSuccessfulChains.sourceClosed initialSelection sourceSelection).mpr initialJoint
  obtain ⟨localTarget,localHistory,edge,selection,_geometry,leaf,lp,active,_child,_lookup,_nonempty,_residual⟩ :=
    PairedMarkerLeafGeometryChecks.Physical.actual_same_producer_active_geometry targetSelection
  obtain ⟨rp⟩ := paired_marker_leaf_geometry leaf localHistory (erase_initLabels source.erase).symm
  have same := paired_marker_first_evaluations leaf leaf lp rp matching selected
    (WrappedSuccessfulChains.initial.outerBarsSafe _) (.nil source) WrappedSuccessfulChains.initial
    WrappedSuccessfulChains.sourceClosed sourceSelection joint.1 selection edge rfl
  exact ⟨sourceSelection,joint,localTarget,localHistory,edge,selection,leaf,lp,rp,same⟩
end InitialPhysical

#print axioms Noninitial.actual_distinct_first_comparison
#print axioms InitialPhysical.actual_initial_joint_comparison
end Lamping.Checks.PairedMarkerFirstComparisonChecks
