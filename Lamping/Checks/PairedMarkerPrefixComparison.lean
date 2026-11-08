import Lamping.Lamping.PairedMarkerPrefixComparison
import Lamping.Checks.PairedMarkerDirectedEvaluation
import Lamping.Lamping.InitialJointRepresentation
import Lamping.Lamping.JointRepresentationTransport
namespace Lamping.Checks.PairedMarkerPrefixComparisonChecks
open AG Graph Lambda Lambda.Labelled
open BetaBeforeBlockImagesChecks

/-- Real INITIAL Joint supplies the induction hypothesis for the SAME
physical evaluator producer in both actual reading directions. Each prefix
comparison is sameleaf integration; the distinct nonINIT test is separate. -/
theorem actual_same_producer_prefixes
    (targetSelection : OccurrenceFragmentSelection target site.reduce (.inl ())) :
    ∃ sourceSelection : OccurrenceFragmentSelection source site.net (.inl ()),
      JointRepresentation WrappedSuccessfulChains.sourceClosed sourceSelection ∧
      ∃ localTarget,History [[.fn]] (initLabels source.erase) localTarget ∧
        ∃ edge : BetaEdge site.net,∃ selection : SourceEdgeSelection (initLabels source.erase) site.net (.inl ()),
          SiteBetaGeometry site edge ∧
          ∃ frontLeaf : DirectedMarkerLeafOutput [[.fn]] source (.atom 2) true [[.fn]] functionTerm.label.letters,
            ∃ front otherFront : PairedMarkerEventGeometry frontLeaf (initLabels source.erase) localTarget,
              selection.evalLabel edge front.alpha=edge.principal ∧
              (orientPhysical true (selection.evalLabel edge front.firstNode.label)++
                  orientPhysical true (front.marker.sourceWord selection.atomWord edge.principal edge.reverseRoute)=
                orientPhysical true (selection.evalLabel edge otherFront.firstNode.label)++
                  orientPhysical true (otherFront.marker.sourceWord selection.atomWord edge.principal edge.reverseRoute)) ∧
              ∃ backLeaf : DirectedMarkerLeafOutput [[.fn]] source (.atom 2) false [[.fn]] (functionTerm.label.readLetters false),
                ∃ back otherBack : PairedMarkerEventGeometry backLeaf (initLabels source.erase) localTarget,
                  (orientPhysical false (selection.evalLabel edge back.firstNode.label)++
                      orientPhysical false (back.marker.sourceWord selection.atomWord edge.principal edge.reverseRoute)=
                    orientPhysical false (selection.evalLabel edge otherBack.firstNode.label)++
                      orientPhysical false (otherBack.marker.sourceWord selection.atomWord edge.principal edge.reverseRoute)) ∧
                  ∃ child,localTarget.subterm [.fn]=some child ∧selection.evalLabel edge child.label≠[] ∧
                    BetaPathResidual site edge
                      ((targetSelection ⟨[.fn],rfl⟩).fragment.segments.map (plugEnd _ _).invFun)
                      (selection.evalLabel edge child.label) := by
  have originalMatches : Matches FunctionWrappedReachable.net (.inl ()) source.erase :=
    encode_closed_matches FunctionWrappedReachable.term FunctionWrappedReachable.closed 0
  have matching := FunctionWrappedReachable.concrete.sourceIso.matches originalMatches
  obtain ⟨initialSelection,initialJoint⟩ := encode_initial_joint_realization source
    WrappedSuccessfulChains.sourceClosed WrappedSuccessfulChains.initial 0
  obtain ⟨sourceSelection⟩ := matching.occurrence_fragment_selection WrappedSuccessfulChains.sourceClosed
  have joint := (FunctionWrappedReachable.concrete.sourceIso.joint_representation originalMatches
    WrappedSuccessfulChains.sourceClosed initialSelection sourceSelection).mpr initialJoint
  obtain ⟨localTarget,history,edge,selection,geometry,frontLeaf,front,active,_frontFormula,
      backLeaf,back,_backFormula,child,lookup,nonempty,residual⟩ :=
    PairedMarkerDirectedEvaluationChecks.actual_same_producer_both_directions targetSelection
  obtain ⟨otherFront⟩ := paired_marker_leaf_geometry frontLeaf history (erase_initLabels source.erase).symm
  obtain ⟨otherBack⟩ := paired_marker_leaf_geometry backLeaf history (erase_initLabels source.erase).symm
  have frontEq := paired_marker_physical_prefixes frontLeaf frontLeaf front otherFront matching selected
    (WrappedSuccessfulChains.initial.outerBarsSafe _) (.nil source) WrappedSuccessfulChains.initial
    WrappedSuccessfulChains.sourceClosed sourceSelection joint.1 selection edge rfl
  have backEq := paired_marker_physical_prefixes backLeaf backLeaf back otherBack matching selected
    (WrappedSuccessfulChains.initial.outerBarsSafe _) (.nil source) WrappedSuccessfulChains.initial
    WrappedSuccessfulChains.sourceClosed sourceSelection joint.1 selection edge rfl
  exact ⟨sourceSelection,joint,localTarget,history,edge,selection,geometry,frontLeaf,front,otherFront,active,
    frontEq,backLeaf,back,otherBack,backEq,child,lookup,nonempty,residual⟩

/-- Real distinct nonINIT leaves retain the explicit source REP hypothesis. -/
theorem actual_noninitial_distinct_prefixes
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    (matching : Matches g root UniformOldCreatedIncomingLabelsChecks.Distinct.source.erase)
    (sourceSelection : OccurrenceFragmentSelection UniformOldCreatedIncomingLabelsChecks.Distinct.source g root)
    (closed : Closed UniformOldCreatedIncomingLabelsChecks.Distinct.source.erase)
    (representation : ChainRepresentationInvariant closed sourceSelection)
    (selection : SourceEdgeSelection (initLabels UniformOldCreatedIncomingLabelsChecks.Distinct.source.erase) g root)
    (edge : BetaEdge g) :
    ∃ localTarget,History [UniformOldCreatedIncomingLabelsChecks.Distinct.left,UniformOldCreatedIncomingLabelsChecks.Distinct.right]
        (initLabels UniformOldCreatedIncomingLabelsChecks.Distinct.source.erase) localTarget ∧
      ∃ lp : PairedMarkerEventGeometry MarkerLeafSourceFirstChainsChecks.leftLeaf
          (initLabels UniformOldCreatedIncomingLabelsChecks.Distinct.source.erase) localTarget,
        ∃ rp : PairedMarkerEventGeometry MarkerLeafSourceFirstChainsChecks.rightLeaf
          (initLabels UniformOldCreatedIncomingLabelsChecks.Distinct.source.erase) localTarget,
          orientPhysical false (selection.evalLabel edge lp.firstNode.label)++
              orientPhysical false (lp.marker.sourceWord selection.atomWord edge.principal edge.reverseRoute)=
            orientPhysical false (selection.evalLabel edge rp.firstNode.label)++
              orientPhysical false (rp.marker.sourceWord selection.atomWord edge.principal edge.reverseRoute) := by
  have sourceSafe := UniformOldCreatedIncomingLabelsChecks.Distinct.source_safe
  obtain ⟨localTarget,history,_erase⟩ := lift_history
    UniformOldCreatedIncomingLabelsChecks.Distinct.labels.betaHistory
    (initLabels UniformOldCreatedIncomingLabelsChecks.Distinct.source.erase)
    (erase_initLabels UniformOldCreatedIncomingLabelsChecks.Distinct.source.erase)
  obtain ⟨lp⟩ := paired_marker_leaf_geometry MarkerLeafSourceFirstChainsChecks.leftLeaf history
    (erase_initLabels UniformOldCreatedIncomingLabelsChecks.Distinct.source.erase).symm
  obtain ⟨rp⟩ := paired_marker_leaf_geometry MarkerLeafSourceFirstChainsChecks.rightLeaf history
    (erase_initLabels UniformOldCreatedIncomingLabelsChecks.Distinct.source.erase).symm
  have equal := paired_marker_physical_prefixes
    MarkerLeafSourceFirstChainsChecks.leftLeaf MarkerLeafSourceFirstChainsChecks.rightLeaf lp rp
    matching UniformOldCreatedIncomingLabelsChecks.Distinct.selected sourceSafe
    UniformOldCreatedIncomingLabelsChecks.Distinct.globalHistory
    UniformOldCreatedIncomingLabelsChecks.Distinct.initial closed sourceSelection representation selection edge rfl
  exact ⟨localTarget,history,lp,rp,equal⟩

#print axioms actual_same_producer_prefixes
#print axioms actual_noninitial_distinct_prefixes
end Lamping.Checks.PairedMarkerPrefixComparisonChecks
