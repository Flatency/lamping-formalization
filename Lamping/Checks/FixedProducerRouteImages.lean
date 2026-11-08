import Lamping.Lamping.FixedProducerRouteImages
import Lamping.Checks.FunctionWrappedReachable
import Lamping.Checks.WrappedSuccessfulChains

namespace Lamping.Checks.FixedProducerRouteImages
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable WrappedSuccessfulChains

private noncomputable abbrev site := FunctionWrappedReachable.concrete.site
private abbrev original := WrappedSuccessfulChains.original
private abbrev current := WrappedSuccessfulChains.current
private abbrev chain := WrappedSuccessfulChains.root_chain
private abbrev member : {p : Path //p∈WrappedSuccessfulChains.rootEdges} := ⟨[.fn],by simp [rootEdges]⟩

/-- Original closed encoding and actual beta event; the nontrivial compound
bar word and SourceRouteImage come from the SAME producer's actual member. -/
theorem actual_closed_fixed_producer_image :
    Closed FunctionWrappedReachable.term ∧
    GraphStep (.beta 0) (ActualNet.initial FunctionWrappedReachable.term)
      (ActualNet.ofNet site.reduce) ∧
    ∃ (targetSelection : OccurrenceFragmentSelection current site.reduce (.inl ()))
      (localTarget : LTerm) (_history : History [[.fn]] (initLabels original.erase) localTarget)
      (edge : BetaEdge site.net)
      (selection : SourceEdgeSelection (initLabels original.erase) site.net (.inl ()))
      (out : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection chain)
      (ctx finish : SourcePort),
      SiteBetaGeometry site edge ∧
      (out.node member).label.letters=
        [.atom 1,.over (.atom 2),.atom 3,.under (.atom 2),.atom 4] ∧
      SourceRouteImage (initLabels original.erase) (.inl ()) edge ctx (out.node member).label finish
        (selection.evalLabel edge (out.node member).label) := by
  refine ⟨FunctionWrappedReachable.closed,FunctionWrappedReachable.actual_beta_step,?_⟩
  obtain ⟨targetSelection⟩ := FunctionWrappedReachable.beta_matches.occurrence_fragment_selection WrappedSuccessfulChains.targetClosed
  obtain ⟨flow⟩ := encode_flowBalance FunctionWrappedReachable.term 0
  obtain ⟨balance⟩ := encode_indexed_balance FunctionWrappedReachable.term 0
  have matching : Matches site.net (.inl ()) original.erase :=
    FunctionWrappedReachable.concrete.sourceIso.matches
      (encode_closed_matches FunctionWrappedReachable.term FunctionWrappedReachable.closed 0)
  obtain ⟨localTarget,history,_erase,_matching,edge,selection,geometry,all⟩ :=
    site.beta_evaluated_chain_residuals (source:=original) (target:=current) FunctionWrappedReachable.closed matching
      (FunctionWrappedReachable.concrete.sourceIso.rootInputs
        (encode_closed_independence FunctionWrappedReachable.term FunctionWrappedReachable.closed 0).rootInputs)
      (FunctionWrappedReachable.concrete.sourceIso.flowBalance flow) rfl
      (FunctionWrappedReachable.concrete.sourceIso.indexed_balance balance) rfl
      (FunctionWrappedReachable.concrete.sourceIso.transparency
        (encode_closed_transparency FunctionWrappedReachable.term FunctionWrappedReachable.closed 0))
      FunctionWrappedReachable.relative (by simp [FunctionWrappedReachable.endpoint,Marked.Normal])
      WrappedSuccessfulChains.actualHistory targetSelection
  obtain ⟨out⟩ := all chain
  have old := (Marked.relativeOld_iff_relative
    (Marked.selected_mark (site.betaSyntaxFiber (.inl ()) original.erase) original.erase)).mpr
      FunctionWrappedReachable.relative
  obtain ⟨ctx,finish,image⟩ := out.fixed_producer_source_route_image site matching old history geometry member
  have sameTarget : localTarget=current := history.deterministic WrappedSuccessfulChains.actualHistory
  obtain ⟨body,atFunction⟩ := WrappedSuccessfulChains.function_lambda_lookup
  have localLookup : current.subterm [.fn]=some (out.node member) :=
    (congrArg (fun t : LTerm=>t.subterm [.fn]) sameTarget).symm.trans (out.lookup member)
  have nodeEq : out.node member=.lam WrappedSuccessfulChains.functionLabel body :=
    Option.some.inj (localLookup.symm.trans atFunction)
  have word : (out.node member).label.letters=
      [.atom 1,.over (.atom 2),.atom 3,.under (.atom 2),.atom 4] := by
    rw [nodeEq];rfl
  exact ⟨targetSelection,localTarget,history,edge,selection,out,ctx,finish,geometry,word,image⟩

#print axioms actual_closed_fixed_producer_image
end Lamping.Checks.FixedProducerRouteImages
