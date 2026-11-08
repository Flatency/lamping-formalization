import Lamping.Lamping.BetaPhysicalCutDecrease
import Lamping.Lamping.ActualWindowResidualOccurrence
import Lamping.Checks.FunctionWrappedReachable
import Lamping.Checks.WrappedSuccessfulChains

namespace Lamping.Checks.BetaPhysicalCutDecrease
open AG Graph Lambda Lambda.Labelled
private noncomputable abbrev site := FunctionWrappedReachable.concrete.site
private abbrev original := WrappedSuccessfulChains.original
private abbrev current := WrappedSuccessfulChains.current
private abbrev chain := WrappedSuccessfulChains.root_chain
private abbrev member : {p : Path //p∈WrappedSuccessfulChains.rootEdges} :=
  ⟨[.fn],by simp [WrappedSuccessfulChains.rootEdges]⟩
private noncomputable abbrev cut := cutFragment site.net
  (pathPartition (Schema.beta 0) FunctionWrappedReachable.concrete.Inside) site.closed

theorem actual_closed_BODY_cut_decreases :
    INIT original ∧Closed original.erase ∧
    GraphStep (.beta 0) (ActualNet.initial FunctionWrappedReachable.term)
      (ActualNet.ofNet site.reduce) ∧
    ∃ (targetSelection : OccurrenceFragmentSelection current site.reduce (.inl ()))
      (localTarget : LTerm) (edge : BetaEdge site.net)
      (selection : SourceEdgeSelection (initLabels original.erase) site.net (.inl ()))
      (_geometry : SiteBetaGeometry site edge)
      (out : EvaluatedChainResiduals site (localTarget:=localTarget)
        edge selection targetSelection chain),
      (out.node member).label=WrappedSuccessfulChains.functionLabel ∧
      ∃cutAt : BetaResidualOccurrence site edge
        ((targetSelection (actualChainPosition chain member)).fragment.segments.map
          (plugEnd cut.label (Schema.beta 0).right.net.label).invFun)
        (selection.evalLabel edge (out.node member).label)
        (.inr (.inl (.inr (.inr true))))
        (([Letter.atom 1,Letter.over (Labelled.Label.atom 2)]).flatMap
          (Letter.sourceWord selection.atomWord edge.principal edge.reverseRoute)).length,
        cutAt.oldBefore=([Letter.atom 1,Letter.over (Labelled.Label.atom 2)]).flatMap
          (Letter.sourceWord selection.atomWord edge.principal edge.reverseRoute) ∧
        rhsVisits (.inl (.inr (.inl (.inr (.inr true))))::cutAt.after) <
          rhsVisits ((targetSelection (actualChainPosition chain member)).fragment.segments.map
            (plugEnd cut.label (Schema.beta 0).right.net.label).invFun) ∧
        ∃ (a b seam : Context) (lc rc : Nat),
          PlugLabelling cut (Schema.beta 0).right.net
            ((targetSelection (actualChainPosition chain member)).fragment.segments.map
              (plugEnd cut.label (Schema.beta 0).right.net.label).invFun) a b ∧
          PlugLabelling cut (Schema.beta 0).right.net
            (cutAt.before++[.inl (.inr (.inl (.inr (.inr true))))]) a seam ∧
          PlugLabelling cut (Schema.beta 0).right.net
            (.inl (.inr (.inl (.inr (.inr true))))::cutAt.after) seam b ∧
          FixedBetaDetourBlocks edge
            (cutAt.oldBefore++[site.outsideEnd (.inr (.inl (.inr (.inr true))))]) a seam lc ∧
          FixedBetaDetourBlocks edge
            (site.outsideEnd (.inr (.inl (.inr (.inr true))))::cutAt.oldAfter) seam b rc
 := by
  refine ⟨WrappedSuccessfulChains.initial,WrappedSuccessfulChains.sourceClosed,
    FunctionWrappedReachable.actual_beta_step,?_⟩
  obtain ⟨targetSelection⟩ := FunctionWrappedReachable.beta_matches.occurrence_fragment_selection
    WrappedSuccessfulChains.targetClosed
  obtain ⟨flow⟩ := encode_flowBalance FunctionWrappedReachable.term 0
  obtain ⟨balance⟩ := encode_indexed_balance FunctionWrappedReachable.term 0
  have matching : Matches site.net (.inl ()) original.erase :=
    FunctionWrappedReachable.concrete.sourceIso.matches
      (encode_closed_matches FunctionWrappedReachable.term FunctionWrappedReachable.closed 0)
  obtain ⟨localTarget,history,_erase,_matching,edge,selection,geometry,all⟩ :=
    site.beta_evaluated_chain_residuals (source:=original) (target:=current)
      FunctionWrappedReachable.closed matching
      (FunctionWrappedReachable.concrete.sourceIso.rootInputs
        (encode_closed_independence FunctionWrappedReachable.term FunctionWrappedReachable.closed 0).rootInputs)
      (FunctionWrappedReachable.concrete.sourceIso.flowBalance flow) rfl
      (FunctionWrappedReachable.concrete.sourceIso.indexed_balance balance) rfl
      (FunctionWrappedReachable.concrete.sourceIso.transparency
        (encode_closed_transparency FunctionWrappedReachable.term FunctionWrappedReachable.closed 0))
      FunctionWrappedReachable.relative
      (by simp [FunctionWrappedReachable.endpoint,Marked.Normal])
      WrappedSuccessfulChains.actualHistory targetSelection
  obtain ⟨out⟩ := all chain
  have equal : localTarget=current := history.deterministic WrappedSuccessfulChains.actualHistory
  have atNode : current.subterm member.val=some (out.node member) :=
    (congrArg (fun t : LTerm=>t.subterm member.val) equal).symm.trans (out.lookup member)
  obtain ⟨body,atLambda⟩ := WrappedSuccessfulChains.function_lambda_lookup
  have nodeEq : out.node member=.lam WrappedSuccessfulChains.functionLabel body :=
    Option.some.inj (atNode.symm.trans atLambda)
  have labelEq : (out.node member).label=WrappedSuccessfulChains.functionLabel := by rw [nodeEq];rfl
  have window : (out.node member).label.letters=
      [Letter.atom 1]++[InteriorSourceBlock.bar true (Labelled.Label.atom 2),.atom 3,
        InteriorSourceBlock.bar false (Labelled.Label.atom 2)]++[Letter.atom 4] := by
    rw [labelEq];rfl
  have old := (Marked.relativeOld_iff_relative
    (Marked.selected_mark (site.betaSyntaxFiber (.inl ()) original.erase) original.erase)).mpr
      FunctionWrappedReachable.relative
  obtain ⟨_atomTail,_atomEq,cutAt,beforeEq,_afterEq,_streams⟩ :=
    out.interior_window_raw_cut site matching edge geometry selection old history targetSelection chain member window
  obtain ⟨routeTail,principalEq⟩ := List.head?_eq_some_iff.mp edge.principalStart
  have firstMem : edge.funEnd∈edge.principal := by
    rw [principalEq]
    exact List.mem_cons_self
  obtain ⟨internal,internalEq⟩ := geometry.principal_internal site _ firstMem
  have inside : site.internalEnd internal∈cutAt.oldBefore := by
    rw [beforeEq]
    change site.internalEnd internal∈selection.atomWord 1++(edge.principal++[])
    rw [List.append_nil,←internalEq]
    exact List.mem_append_right _ firstMem
  obtain ⟨strict,_counts,split⟩ := cutAt.strict_rhs_cut site geometry ⟨internal,inside⟩
  let fragment := (targetSelection (actualChainPosition chain member)).fragment
  obtain ⟨a,b,whole⟩ := fragment.access.property.1.1
  obtain ⟨input,_prefix,part⟩ := fragment.assignments a b whole
  have rawLabels := part.plug_decomposition cut (Schema.beta 0).right.net
  obtain ⟨seam,lc,rc,leftRaw,rightRaw,leftOld,rightOld⟩ := split rawLabels
  exact ⟨targetSelection,localTarget,edge,selection,geometry,out,labelEq,cutAt,beforeEq,
    strict,input,b,seam,lc,rc,rawLabels,leftRaw,rightRaw,leftOld,rightOld⟩

#print axioms actual_closed_BODY_cut_decreases
end Lamping.Checks.BetaPhysicalCutDecrease
