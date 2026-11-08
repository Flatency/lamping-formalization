import Lamping.Lamping.PairedMarkerLeafGeometry
import Lamping.Checks.MarkerSourceChainLabels
import Lamping.Checks.BetaBeforeBlockImages
namespace Lamping.Checks.PairedMarkerLeafGeometryChecks
open Graph Lambda Lambda.Labelled AG

namespace Noninitial
open UniformOldCreatedIncomingLabelsChecks.Distinct

/-- A real original INIT prefix followed by two OLD events. The relative
source is nonINIT; its paired local history is produced by actual lifting.
This exercises event geometry, not a nonINIT physical-site realization. -/
theorem actual_noninitial_pair :
    INIT original ∧History [[]] original source ∧source≠initLabels source.erase ∧
    ∃ localTarget,History [left,right] (initLabels source.erase) localTarget ∧
      ∃ leaf : DirectedMarkerLeafOutput F source (.atom 7) false [left,right] (leftNode.label.readLetters false),
        Nonempty (PairedMarkerEventGeometry leaf (initLabels source.erase) localTarget) := by
  refine ⟨initial,globalHistory,by decide,?_⟩
  obtain ⟨localTarget,localHistory,_erase⟩ := lift_history labels.betaHistory (initLabels source.erase) (erase_initLabels source.erase)
  obtain ⟨leaf⟩ := DirectedMarkerLeafTailsChecks.Distinct.leftProduced
  exact ⟨localTarget,localHistory,leaf,paired_marker_leaf_geometry leaf localHistory (erase_initLabels source.erase).symm⟩

end Noninitial

namespace CopiedZero
abbrev body : LTerm := .var (.atom 8) 0
abbrev argument : LTerm := .lam (.atom 9) (.var (.atom 10) 0)
abbrev localBody : LTerm := .var (.atom 80) 0
abbrev localArgument : LTerm := .lam (.atom 90) (.var (.atom 100) 0)

/-- The given copied-root origin keeps ARG as FIRST and BODY as LAST after
reannotation, even though the same edge also permits a result-root origin. -/
theorem exact_copied_zero_coordinates :
    BetaIncomingReadingOrigin localBody localArgument [] [] [] [.arg] [.arg] [.fn,.body] := by
  have origin : BetaIncomingReadingOrigin body argument [] [] [] [.arg] [.arg] [.fn,.body] :=
    .copyLambda (q:=[]) rfl rfl rfl rfl
  exact origin.reannotated rfl rfl

theorem distinct_local_labels : body.label≠localBody.label ∧argument.label≠localArgument.label := by decide
end CopiedZero

namespace Physical
open BetaBeforeBlockImagesChecks
private def position : Position target.erase := ⟨[.fn],rfl⟩

/-- The SAME actual full local evaluator producer supplies both the marked
child residual and the event's active principal evaluation. This physical
consumer has an initial relative source; the nonINIT consumer above is pure. -/
theorem actual_same_producer_active_geometry
    (targetSelection : OccurrenceFragmentSelection target site.reduce (.inl ())) :
    ∃ localTarget,History [[.fn]] (initLabels source.erase) localTarget ∧
      ∃ edge : BetaEdge site.net,∃ selection : SourceEdgeSelection (initLabels source.erase) site.net (.inl ()),
        SiteBetaGeometry site edge ∧
        ∃ leaf : DirectedMarkerLeafOutput [[.fn]] source (.atom 2) true [[.fn]] functionTerm.label.letters,
          ∃ paired : PairedMarkerEventGeometry leaf (initLabels source.erase) localTarget,
            selection.evalLabel edge paired.alpha=edge.principal ∧
            ∃ localChild,localTarget.subterm [.fn]=some localChild ∧
              selection.evalLabel edge localChild.label≠[] ∧
              BetaPathResidual site edge
                ((targetSelection position).fragment.segments.map (plugEnd _ _).invFun)
                (selection.evalLabel edge localChild.label) := by
  have matching := FunctionWrappedReachable.concrete.sourceIso.matches
    (encode_closed_matches FunctionWrappedReachable.term FunctionWrappedReachable.closed 0)
  have inputs := FunctionWrappedReachable.concrete.sourceIso.rootInputs
    (encode_closed_independence FunctionWrappedReachable.term FunctionWrappedReachable.closed 0).rootInputs
  obtain ⟨originalFlow⟩ := encode_flowBalance FunctionWrappedReachable.term 0
  have flow := FunctionWrappedReachable.concrete.sourceIso.flowBalance originalFlow
  obtain ⟨originalBalance⟩ := encode_indexed_balance FunctionWrappedReachable.term 0
  have balance := FunctionWrappedReachable.concrete.sourceIso.indexed_balance originalBalance
  have transparency := FunctionWrappedReachable.concrete.sourceIso.transparency
    (encode_closed_transparency FunctionWrappedReachable.term FunctionWrappedReachable.closed 0)
  obtain ⟨localTarget,localHistory,_erase,_matching,edge,selection,geometry,all⟩ :=
    site.beta_evaluated_child_residuals WrappedSuccessfulChains.sourceClosed matching inputs flow rfl balance rfl
      transparency FunctionWrappedReachable.relative (by simp [FunctionWrappedReachable.endpoint,Marked.Normal])
      WrappedSuccessfulChains.actualHistory
  have spine : DirectedMarkerSpine [[.fn]] source (.atom 2) true [[.fn]] target [] [.fn] :=
    old.directed_marker_spine WrappedSuccessfulChains.actualHistory selected
      (WrappedSuccessfulChains.initial.outerBarsSafe _) (start:=[]) (before:=[]) .refl
      ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ rfl marked (by intro e member;cases member)
  obtain ⟨leaf⟩ := spine.leaf_output (by rfl : target.subterm [.fn]=some functionTerm)
  obtain ⟨paired,active⟩ := site.paired_marker_leaf_active_geometry leaf localHistory matching
    FunctionWrappedReachable.relative edge geometry selection
  let child := targetSelection position
  have occurrence : SourceSubterm [] .external target [.fn] [] (.appFn (.atom 0)) functionTerm := .fn .nil
  obtain ⟨_environment,context,_term⟩ := child.occurrence.same_occurrence occurrence
  have fromEq : (sourceEdge child.environment child.context child.term).fromPort=child.context := by
    cases child.term <;> rfl
  have role : SourceDeparture target .fn (sourceEdge child.environment child.context child.term).fromPort := by
    rw [fromEq,context];exact .fn
  obtain ⟨localChild,lookup,_erase,nonempty,residual⟩ := all [] .fn target rfl child role
  exact ⟨localTarget,localHistory,edge,selection,geometry,leaf,paired,active,localChild,lookup,nonempty,residual⟩
end Physical

#print axioms Noninitial.actual_noninitial_pair
#print axioms CopiedZero.exact_copied_zero_coordinates
#print axioms CopiedZero.distinct_local_labels
#print axioms Physical.actual_same_producer_active_geometry
end Lamping.Checks.PairedMarkerLeafGeometryChecks
