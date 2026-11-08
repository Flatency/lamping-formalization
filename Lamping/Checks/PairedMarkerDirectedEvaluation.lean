import Lamping.Lamping.PairedMarkerDirectedEvaluation
import Lamping.Checks.PairedMarkerLeafGeometry
import Lamping.Checks.PairedMarkerFirstComparison

namespace Lamping.Checks.PairedMarkerDirectedEvaluationChecks
open AG Graph Lambda Lambda.Labelled
open BetaBeforeBlockImagesChecks

/-- Both actual reading directions at the SAME physical producer. The
reverse leaf has its own real lambda reading; it is not a flipped Bool on
the forward leaf. Both complete local overlap formulas are interpreted. -/
theorem actual_same_producer_both_directions
    (targetSelection : OccurrenceFragmentSelection target site.reduce (.inl ())) :
    ∃ localTarget,History [[.fn]] (initLabels source.erase) localTarget ∧
      ∃ edge : BetaEdge site.net,∃ selection : SourceEdgeSelection (initLabels source.erase) site.net (.inl ()),
        SiteBetaGeometry site edge ∧
        ∃ forwardLeaf : DirectedMarkerLeafOutput [[.fn]] source (.atom 2) true [[.fn]] functionTerm.label.letters,
          ∃ front : PairedMarkerEventGeometry forwardLeaf (initLabels source.erase) localTarget,
            selection.evalLabel edge front.alpha=edge.principal ∧
            ExactPhysicalDirectedFormula selection edge front.middle forwardLeaf.site front.alpha true
              front.firstNode front.lastNode front.marker front.current ∧
            ∃ backwardLeaf : DirectedMarkerLeafOutput [[.fn]] source (.atom 2) false [[.fn]] (functionTerm.label.readLetters false),
              ∃ back : PairedMarkerEventGeometry backwardLeaf (initLabels source.erase) localTarget,
                ExactPhysicalDirectedFormula selection edge back.middle backwardLeaf.site back.alpha false
                  back.firstNode back.lastNode back.marker back.current ∧
                ∃ localChild,localTarget.subterm [.fn]=some localChild ∧
                  selection.evalLabel edge localChild.label≠[] ∧
                  BetaPathResidual site edge
                    ((targetSelection ⟨[.fn],rfl⟩).fragment.segments.map (plugEnd _ _).invFun)
                    (selection.evalLabel edge localChild.label) := by
  obtain ⟨localTarget,localHistory,edge,selection,geometry,forwardLeaf,front,active,child,lookup,nonempty,residual⟩ :=
    PairedMarkerLeafGeometryChecks.Physical.actual_same_producer_active_geometry targetSelection
  have spine : DirectedMarkerSpine [[.fn]] source (.atom 2) false [[.fn]] target [] [.fn] :=
    old.directed_marker_spine WrappedSuccessfulChains.actualHistory selected
      (WrappedSuccessfulChains.initial.outerBarsSafe _) (start:=[.fn]) (before:=[]) .refl
      ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩ rfl marked (by intro e member;cases member)
  obtain ⟨backwardLeaf⟩ := spine.leaf_output (by rfl : target.subterm [.fn]=some functionTerm)
  obtain ⟨back⟩ := paired_marker_leaf_geometry backwardLeaf localHistory (erase_initLabels source.erase).symm
  exact ⟨localTarget,localHistory,edge,selection,geometry,forwardLeaf,front,active,
    AG.PairedMarkerEventGeometry.physical_formula front selection edge,backwardLeaf,back,AG.PairedMarkerEventGeometry.physical_formula back selection edge,
    child,lookup,nonempty,residual⟩

/-- Real distinct nonINIT leaves retain the explicit source REP hypothesis. -/
theorem actual_noninitial_oriented_first
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
          orientPhysical false (selection.evalLabel edge lp.firstNode.label)=
            orientPhysical false (selection.evalLabel edge rp.firstNode.label) := by
  have sourceSafe := UniformOldCreatedIncomingLabelsChecks.Distinct.source_safe
  obtain ⟨localTarget,history,_erase⟩ := lift_history
    UniformOldCreatedIncomingLabelsChecks.Distinct.labels.betaHistory
    (initLabels UniformOldCreatedIncomingLabelsChecks.Distinct.source.erase)
    (erase_initLabels UniformOldCreatedIncomingLabelsChecks.Distinct.source.erase)
  obtain ⟨lp⟩ := paired_marker_leaf_geometry MarkerLeafSourceFirstChainsChecks.leftLeaf history
    (erase_initLabels UniformOldCreatedIncomingLabelsChecks.Distinct.source.erase).symm
  obtain ⟨rp⟩ := paired_marker_leaf_geometry MarkerLeafSourceFirstChainsChecks.rightLeaf history
    (erase_initLabels UniformOldCreatedIncomingLabelsChecks.Distinct.source.erase).symm
  have equal := paired_marker_first_oriented_evaluations
    MarkerLeafSourceFirstChainsChecks.leftLeaf MarkerLeafSourceFirstChainsChecks.rightLeaf lp rp
    matching UniformOldCreatedIncomingLabelsChecks.Distinct.selected sourceSafe
    UniformOldCreatedIncomingLabelsChecks.Distinct.globalHistory
    UniformOldCreatedIncomingLabelsChecks.Distinct.initial closed sourceSelection representation selection edge rfl
  exact ⟨localTarget,history,lp,rp,equal⟩

#print axioms actual_same_producer_both_directions
#print axioms actual_noninitial_oriented_first
end Lamping.Checks.PairedMarkerDirectedEvaluationChecks
