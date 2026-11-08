import Lamping.Lamping.BetaEvaluatedChildResiduals
import Lamping.Checks.BetaBeforeBlockImages
namespace Lamping.Checks.BetaEvaluatedChildResidualsChecks
open AG Graph Lambda Lambda.Labelled BetaBeforeBlockImagesChecks

private def functionPosition : Position target.erase := ⟨[.fn],rfl⟩

/-- A genuine marked FUNCTION child on the concrete initial beta trace.
The source is already its initial annotation, so SAME-schedule determinism
identifies the local evaluator label; no family identity is reset. -/
theorem actual_marked_function_evaluator
    (targetSelection : OccurrenceFragmentSelection target site.reduce (.inl ())) :
    ∃ edge : BetaEdge site.net,∃ selection : SourceEdgeSelection (initLabels source.erase) site.net (.inl ()),
      SiteBetaGeometry site edge ∧selection.evalLabel edge WrappedSuccessfulChains.functionLabel≠[] ∧
      BetaPathResidual site edge
        ((targetSelection functionPosition).fragment.segments.map (plugEnd _ _).invFun)
        (selection.evalLabel edge WrappedSuccessfulChains.functionLabel) := by
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
  obtain ⟨localTarget,localLabels,_sameErase,_matching,edge,selection,geometry,all⟩ :=
    site.beta_evaluated_child_residuals WrappedSuccessfulChains.sourceClosed matching inputs flow rfl
      balance rfl transparency FunctionWrappedReachable.relative
      (by simp [FunctionWrappedReachable.endpoint,Marked.Normal]) WrappedSuccessfulChains.actualHistory
  change History [[.fn]] source localTarget at localLabels
  have same := localLabels.deterministic WrappedSuccessfulChains.actualHistory
  subst localTarget
  let child := targetSelection functionPosition
  have occurrence : SourceSubterm [] .external target [.fn] [] (.appFn (.atom 0)) functionTerm := .fn .nil
  obtain ⟨_environment,context,_term⟩ := child.occurrence.same_occurrence occurrence
  have fromEq : (sourceEdge child.environment child.context child.term).fromPort=child.context := by
    cases child.term <;> rfl
  have role : SourceDeparture target .fn (sourceEdge child.environment child.context child.term).fromPort := by
    rw [fromEq,context]
    exact .fn
  obtain ⟨localChild,lookup,_erase,nonempty,residual⟩ := all [] .fn target rfl child role
  have eq : localChild=functionTerm := Option.some.inj lookup.symm
  subst localChild
  exact ⟨edge,selection,geometry,nonempty,residual⟩

/-- This consumer uses the marked domain excluded by the older safe-child
producer. Its literal evaluator includes both principal directions. -/
theorem actual_marked_function_literal
    (targetSelection : OccurrenceFragmentSelection target site.reduce (.inl ())) :
    ¬functionTerm.label.OuterBarsSafe (fun x=>x≠Label.atom 2) ∧
    ∃ edge : BetaEdge site.net,∃ selection : SourceEdgeSelection (initLabels source.erase) site.net (.inl ()),
      SiteBetaGeometry site edge ∧
      BetaPathResidual site edge
        ((targetSelection functionPosition).fragment.segments.map (plugEnd _ _).invFun)
        ((selection.atomWord 1++edge.principal)++
          ((selection.atomWord 3++edge.reverseRoute)++selection.atomWord 4)) := by
  obtain ⟨edge,selection,geometry,_nonempty,residual⟩ := actual_marked_function_evaluator targetSelection
  refine ⟨marked,edge,selection,geometry,?_⟩
  simpa only [WrappedSuccessfulChains.functionLabel,SourceEdgeSelection.evalLabel,
    Label.sourceWord_concat,Label.atom,Label.over,Label.under,Label.sourceWord,
    Letter.sourceWord,List.append_assoc] using residual

#print axioms actual_marked_function_evaluator
#print axioms actual_marked_function_literal
end Lamping.Checks.BetaEvaluatedChildResidualsChecks
