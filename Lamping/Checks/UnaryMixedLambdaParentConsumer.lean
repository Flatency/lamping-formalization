import Lamping.Lamping.UnaryMixedLambdaParentSeparation
import Lamping.Checks.UnaryLambdaBodyConsumer
set_option maxHeartbeats 4000000
namespace Lamping.Checks.UnaryMixedLambdaParentConsumer.Cro
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable
open UnaryBindingReachable.Cro UnaryLambdaBodyConsumer.Cro
theorem actual_unrestricted_mixed_pair
    (sourceBody : SourceEdgeFragment current croLambda.site.net (.inl ()) edge position)
    (targetBody : SourceEdgeFragment current croLambda.site.reduce (.inl ()) edge position)
    (sourceFunction : SourceEdgeFragment current croLambda.site.net (.inl ()) rootFunctionEdge [.fn])
    (targetFunction : SourceEdgeFragment current croLambda.site.reduce (.inl ()) rootFunctionEdge [.fn]) :
    sourceBody.segments≠sourceFunction.segments ∧targetBody.segments≠targetFunction.segments ∧
    (targetBody.segments=targetFunction.segments ↔sourceBody.segments=sourceFunction.segments) := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  obtain ⟨principal⟩ := croLambda.site.actionPrincipal_exists
  let parentPosition : Position current.erase := ⟨[.fn],rfl⟩
  obtain ⟨sourceParent,parentWord,_⟩ := Matches.observation croLambda.site.net source_matches parentPosition
  have oldBodyWord : position=accessWord croLambda.site.net sourceParent.val++[.body] := by rw [parentWord];rfl
  have newBodyWord : position=accessWord croLambda.site.reduce lambdaParent.val++[.body] := by
    change position=accessWord croLambda.site.reduce lambdaEdges++[.body]
    rw [lambdaWord];rfl
  obtain ⟨oldRoot,oldPort,oldWord,oldFinish⟩ := actual_source_root_parent
  obtain ⟨oldRoot,oldPort,oldWord,oldFinish⟩ := actual_source_root_parent
  obtain ⟨newRoot,newPort,newWord,newFinish⟩ := UnaryLambdaContextConsumer.Cro.actual_kept_root_parent
  have oldFnWord : [.fn]=accessWord croLambda.site.net oldRoot.val++[.fn] := by rw [oldWord];rfl
  have newFnWord : [.fn]=accessWord croLambda.site.reduce newRoot.val++[.fn] := by rw [newWord];rfl
  exact sourceBody.cro_copied_lambda_parent_vs_kept_parent croLambda.site
    (croLambda.sourceIso.flowBalance flow) (.inl ()) rfl source_matches target_matches principal
    targetBody sourceFunction targetFunction role root_function_role
    sourceParent lambdaParent oldRoot newRoot
    oldBodyWord newBodyWord
    oldFnWord
    newFnWord lambdaFinish newPort.1 newPort.2 newFinish

theorem actual_reachable_mixed_supply :
    INIT original ∧ Closed original.erase ∧ History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet croLambda.site.reduce)
      [.beta 0,.croAction .lam 0 1 (by decide)] ∧
    Matches croLambda.site.net (.inl ()) current.erase ∧
    Matches croLambda.site.reduce (.inl ()) current.erase ∧
    AuxiliaryAt current position ∧
    EndpointChain current (SyntaxIncidence.source current bodyEdge) [[.fn]] ∧
    EndpointChain current (SyntaxIncidence.target current WrappedSuccessfulChains.targetClosed bodyEdge) WrappedSuccessfulChains.bodyEdges ∧
    Nonempty (SourceEdgeFragment current croLambda.site.net (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current croLambda.site.reduce (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current croLambda.site.net (.inl ()) rootFunctionEdge [.fn]) ∧
    Nonempty (SourceEdgeFragment current croLambda.site.reduce (.inl ()) rootFunctionEdge [.fn]) ∧
    position≠[.fn] ∧
    ∀ (sourceBody : SourceEdgeFragment current croLambda.site.net (.inl ()) edge position)
      (targetBody : SourceEdgeFragment current croLambda.site.reduce (.inl ()) edge position)
      (sourceFunction : SourceEdgeFragment current croLambda.site.net (.inl ()) rootFunctionEdge [.fn])
      (targetFunction : SourceEdgeFragment current croLambda.site.reduce (.inl ()) rootFunctionEdge [.fn]),
      sourceBody.segments≠sourceFunction.segments ∧targetBody.segments≠targetFunction.segments ∧
      (targetBody.segments=targetFunction.segments ↔sourceBody.segments=sourceFunction.segments) := by
  obtain ⟨oldBody,newBody,oldFn,newFn,different⟩ := actual_four_mixed_fragments
  obtain ⟨sourceChain,targetChain⟩ := endpoint_chains
  exact ⟨WrappedSuccessfulChains.initial,WrappedSuccessfulChains.sourceClosed,WrappedSuccessfulChains.actualHistory,
    UnaryBindingConsumer.Cro.actual_two_rule_trace,source_matches,target_matches,auxiliary,
    sourceChain,targetChain,oldBody,newBody,oldFn,newFn,different,actual_unrestricted_mixed_pair⟩

#print axioms actual_reachable_mixed_supply
#print axioms actual_unrestricted_mixed_pair
end Lamping.Checks.UnaryMixedLambdaParentConsumer.Cro
namespace Lamping.Checks.UnaryMixedLambdaParentConsumer.Bra
open AG Graph Lambda Lambda.Labelled BraFunctionReachable
open UnaryBindingReachable.Bra UnaryLambdaBodyConsumer.Bra
theorem actual_unrestricted_mixed_pair
    (sourceBody : SourceEdgeFragment current braLambda.site.net (.inl ()) edge position)
    (targetBody : SourceEdgeFragment current braLambda.site.reduce (.inl ()) edge position)
    (sourceFunction : SourceEdgeFragment current braLambda.site.net (.inl ()) rootFunctionEdge [.fn])
    (targetFunction : SourceEdgeFragment current braLambda.site.reduce (.inl ()) rootFunctionEdge [.fn]) :
    sourceBody.segments≠sourceFunction.segments ∧targetBody.segments≠targetFunction.segments ∧
    (targetBody.segments=targetFunction.segments ↔sourceBody.segments=sourceFunction.segments) := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  obtain ⟨principal⟩ := braLambda.site.actionPrincipal_exists
  let parentPosition : Position current.erase := ⟨[.arg],rfl⟩
  obtain ⟨sourceParent,parentWord,_⟩ := Matches.observation braLambda.site.net source_matches parentPosition
  have oldBodyWord : position=accessWord braLambda.site.net sourceParent.val++[.body] := by rw [parentWord];rfl
  have newBodyWord : position=accessWord braLambda.site.reduce lambdaParent.val++[.body] := by
    change position=accessWord braLambda.site.reduce lambdaEdges++[.body]
    rw [lambdaWord];rfl
  obtain ⟨oldRoot,oldPort,oldWord,oldFinish⟩ := actual_source_root_parent
  obtain ⟨oldRoot,oldPort,oldWord,oldFinish⟩ := actual_source_root_parent
  obtain ⟨newRoot,newPort,newWord,newFinish⟩ := UnaryLambdaContextConsumer.Bra.actual_kept_root_parent
  have oldFnWord : [.fn]=accessWord braLambda.site.net oldRoot.val++[.fn] := by rw [oldWord];rfl
  have newFnWord : [.fn]=accessWord braLambda.site.reduce newRoot.val++[.fn] := by rw [newWord];rfl
  exact sourceBody.bra_copied_lambda_parent_vs_kept_parent braLambda.site
    (braLambda.sourceIso.flowBalance flow) (.inl ()) rfl source_matches target_matches principal
    targetBody sourceFunction targetFunction role root_function_role
    sourceParent lambdaParent oldRoot newRoot
    oldBodyWord newBodyWord
    oldFnWord
    newFnWord lambdaFinish newPort.1 newPort.2 newFinish

theorem actual_reachable_mixed_supply :
    INIT original ∧ Closed original.erase ∧ History [[]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet braLambda.site.reduce)
      [.beta 0,.braAction .lam 0 1 (by decide)] ∧
    Matches braLambda.site.net (.inl ()) current.erase ∧
    Matches braLambda.site.reduce (.inl ()) current.erase ∧
    AuxiliaryAt current position ∧
    EndpointChain current (SyntaxIncidence.source current bodyEdge) [[.arg],[.fn]] ∧
    EndpointChain current (SyntaxIncidence.target current BraSuccessfulChains.targetClosed bodyEdge) BraSuccessfulChains.bodyEdges ∧
    Nonempty (SourceEdgeFragment current braLambda.site.net (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current braLambda.site.reduce (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current braLambda.site.net (.inl ()) rootFunctionEdge [.fn]) ∧
    Nonempty (SourceEdgeFragment current braLambda.site.reduce (.inl ()) rootFunctionEdge [.fn]) ∧
    position≠[.fn] ∧
    ∀ (sourceBody : SourceEdgeFragment current braLambda.site.net (.inl ()) edge position)
      (targetBody : SourceEdgeFragment current braLambda.site.reduce (.inl ()) edge position)
      (sourceFunction : SourceEdgeFragment current braLambda.site.net (.inl ()) rootFunctionEdge [.fn])
      (targetFunction : SourceEdgeFragment current braLambda.site.reduce (.inl ()) rootFunctionEdge [.fn]),
      sourceBody.segments≠sourceFunction.segments ∧targetBody.segments≠targetFunction.segments ∧
      (targetBody.segments=targetFunction.segments ↔sourceBody.segments=sourceFunction.segments) := by
  obtain ⟨oldBody,newBody,oldFn,newFn,different⟩ := actual_four_mixed_fragments
  obtain ⟨sourceChain,targetChain⟩ := endpoint_chains
  exact ⟨BraSuccessfulChains.initial,BraSuccessfulChains.sourceClosed,BraSuccessfulChains.actualHistory,
    UnaryBindingConsumer.Bra.actual_two_rule_trace,source_matches,target_matches,auxiliary,
    sourceChain,targetChain,oldBody,newBody,oldFn,newFn,different,actual_unrestricted_mixed_pair⟩

#print axioms actual_reachable_mixed_supply
#print axioms actual_unrestricted_mixed_pair
end Lamping.Checks.UnaryMixedLambdaParentConsumer.Bra
