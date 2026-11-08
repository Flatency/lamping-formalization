import Lamping.Lamping.UnaryMixedAppTerminalSeparation
import Lamping.Checks.UnaryAppContextConsumer
import Lamping.Checks.FunctionWrappedMixedConsumer
set_option maxHeartbeats 4000000
namespace Lamping.Checks.UnaryMixedAppTerminalConsumer.Cro
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable
open UnaryAppContextConsumer.Cro
abbrev otherEdge := FunctionWrappedMixedConsumer.rootEdge
def otherOccurrence := FunctionWrappedMixedConsumer.rootOccurrence

theorem actual_kept_lambda_finish
    (target : SourceEdgeFragment current croApp.site.reduce (.inl ()) otherEdge [.fn]) :
    target.access.val.getLast?=some (croApp.site.reduce.wire
      (.inl ⟨.inl FunctionWrappedBodyParent.copiedLambda4,.inl ()⟩)) := by
  have same : WrappedLambdaParent.finalParent=target.access :=
    actual_final_matches.accessWord_injective (WrappedLambdaParent.finalWord.trans target.word.symm)
  rw [←same]
  exact WrappedLambdaParent.finalFinish

theorem actual_mixed_terminal_pair
    (sourceBody : SourceEdgeFragment current croApp.site.net (.inl ()) edge position)
    (targetBody : SourceEdgeFragment current croApp.site.reduce (.inl ()) edge position)
    (sourceOther : SourceEdgeFragment current croApp.site.net (.inl ()) otherEdge [.fn])
    (targetOther : SourceEdgeFragment current croApp.site.reduce (.inl ()) otherEdge [.fn]) :
    sourceBody.segments≠sourceOther.segments ∧targetBody.segments≠targetOther.segments ∧
      (targetBody.segments=targetOther.segments ↔sourceBody.segments=sourceOther.segments) := by
  obtain ⟨flow,_,_,_,_⟩ := cro_certified
  obtain ⟨principal⟩ := croApp.site.actionPrincipal_exists
  exact sourceBody.cro_copied_app_terminal_vs_kept_terminal croApp.site
    (croApp.sourceIso.flowBalance flow) (.inl ()) rfl FunctionWrappedConsumer.source_matches principal
    targetBody sourceOther targetOther (actual_copied_app_finish targetBody)
    FunctionWrappedBodyParent.copiedLambda4 (.inl ()) (actual_kept_lambda_finish targetOther)

theorem actual_reachable_mixed_terminal_supply :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet croApp.site.reduce)
      [.beta 0,.croAction .lam 0 1 (by decide),.croAction .cro 0 1 (by decide),.croAction .app 0 1 (by decide)] ∧
    Matches croApp.site.net (.inl ()) current.erase ∧Matches croApp.site.reduce (.inl ()) current.erase ∧
    AuxiliaryAt current position ∧
    EndpointChain current (SyntaxIncidence.source current bodyEdge) [[.fn]] ∧
    EndpointChain current (SyntaxIncidence.target current WrappedSuccessfulChains.targetClosed bodyEdge) WrappedSuccessfulChains.bodyEdges ∧
    Nonempty (SourceEdgeFragment current croApp.site.net (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current croApp.site.reduce (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current croApp.site.net (.inl ()) otherEdge [.fn]) ∧
    Nonempty (SourceEdgeFragment current croApp.site.reduce (.inl ()) otherEdge [.fn]) ∧
    position≠[.fn] ∧
    ∀ (sourceBody : SourceEdgeFragment current croApp.site.net (.inl ()) edge position)
      (targetBody : SourceEdgeFragment current croApp.site.reduce (.inl ()) edge position)
      (sourceOther : SourceEdgeFragment current croApp.site.net (.inl ()) otherEdge [.fn])
      (targetOther : SourceEdgeFragment current croApp.site.reduce (.inl ()) otherEdge [.fn]),
      sourceBody.segments≠sourceOther.segments ∧targetBody.segments≠targetOther.segments ∧
      (targetBody.segments=targetOther.segments ↔sourceBody.segments=sourceOther.segments) := by
  obtain ⟨oldBody,newBody⟩ := actual_fragments
  obtain ⟨sourceChain,targetChain⟩ := UnaryLambdaBodyConsumer.Cro.endpoint_chains
  exact ⟨WrappedSuccessfulChains.initial,WrappedSuccessfulChains.sourceClosed,WrappedSuccessfulChains.actualHistory,actual_four_step_trace,
    FunctionWrappedConsumer.source_matches,actual_final_matches,auxiliary,sourceChain,targetChain,oldBody,newBody,
    FunctionWrappedConsumer.source_matches.base_source_edge_fragment WrappedSuccessfulChains.targetClosed otherOccurrence,
    actual_final_matches.base_source_edge_fragment WrappedSuccessfulChains.targetClosed otherOccurrence,
    by decide,actual_mixed_terminal_pair⟩

#print axioms actual_reachable_mixed_terminal_supply
#print axioms actual_kept_lambda_finish
#print axioms actual_mixed_terminal_pair
end Lamping.Checks.UnaryMixedAppTerminalConsumer.Cro
namespace Lamping.Checks.UnaryMixedAppTerminalConsumer.Bra
open AG Graph Lambda Lambda.Labelled BraFunctionReachable
open UnaryAppContextConsumer.Bra
abbrev otherTerm : LTerm := match current with
  | .app _ _ arg => arg
  | t => t
abbrev otherEdge := sourceEdge [] (.appArg current.label) otherTerm
def otherOccurrence : SourceSubterm [] .external current [.arg] [] (.appArg current.label) otherTerm := .arg .nil

theorem actual_kept_lambda_finish
    (target : SourceEdgeFragment current braApp.site.reduce (.inl ()) otherEdge [.arg]) :
    target.access.val.getLast?=some (braApp.site.reduce.wire
      (.inl ⟨.inl BraFunctionBodyParent.copiedLambda4,.inl ()⟩)) := by
  have same : BraArgumentParent.finalParent=target.access :=
    actual_final_matches.accessWord_injective (BraArgumentParent.finalWord.trans target.word.symm)
  rw [←same]
  exact BraArgumentParent.finalFinish

theorem actual_mixed_terminal_pair
    (sourceBody : SourceEdgeFragment current braApp.site.net (.inl ()) edge position)
    (targetBody : SourceEdgeFragment current braApp.site.reduce (.inl ()) edge position)
    (sourceOther : SourceEdgeFragment current braApp.site.net (.inl ()) otherEdge [.arg])
    (targetOther : SourceEdgeFragment current braApp.site.reduce (.inl ()) otherEdge [.arg]) :
    sourceBody.segments≠sourceOther.segments ∧targetBody.segments≠targetOther.segments ∧
      (targetBody.segments=targetOther.segments ↔sourceBody.segments=sourceOther.segments) := by
  obtain ⟨flow,_,_,_,_⟩ := cro_certified
  obtain ⟨principal⟩ := braApp.site.actionPrincipal_exists
  exact sourceBody.bra_copied_app_terminal_vs_kept_terminal braApp.site
    (braApp.sourceIso.flowBalance flow) (.inl ()) rfl BraFunctionConsumer.source_matches principal
    targetBody sourceOther targetOther (actual_copied_app_finish targetBody)
    BraFunctionBodyParent.copiedLambda4 (.inl ()) (actual_kept_lambda_finish targetOther)

theorem actual_reachable_mixed_terminal_supply :
    INIT original ∧Closed original.erase ∧History [[]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet braApp.site.reduce)
      [.beta 0,.braAction .lam 0 1 (by decide),.braAction .cro 0 1 (by decide),.braAction .app 0 1 (by decide)] ∧
    Matches braApp.site.net (.inl ()) current.erase ∧Matches braApp.site.reduce (.inl ()) current.erase ∧
    AuxiliaryAt current position ∧
    EndpointChain current (SyntaxIncidence.source current bodyEdge) [[.arg],[.fn]] ∧
    EndpointChain current (SyntaxIncidence.target current BraSuccessfulChains.targetClosed bodyEdge) BraSuccessfulChains.bodyEdges ∧
    Nonempty (SourceEdgeFragment current braApp.site.net (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current braApp.site.reduce (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current braApp.site.net (.inl ()) otherEdge [.arg]) ∧
    Nonempty (SourceEdgeFragment current braApp.site.reduce (.inl ()) otherEdge [.arg]) ∧
    position≠[.arg] ∧
    ∀ (sourceBody : SourceEdgeFragment current braApp.site.net (.inl ()) edge position)
      (targetBody : SourceEdgeFragment current braApp.site.reduce (.inl ()) edge position)
      (sourceOther : SourceEdgeFragment current braApp.site.net (.inl ()) otherEdge [.arg])
      (targetOther : SourceEdgeFragment current braApp.site.reduce (.inl ()) otherEdge [.arg]),
      sourceBody.segments≠sourceOther.segments ∧targetBody.segments≠targetOther.segments ∧
      (targetBody.segments=targetOther.segments ↔sourceBody.segments=sourceOther.segments) := by
  obtain ⟨oldBody,newBody⟩ := actual_fragments
  obtain ⟨sourceChain,targetChain⟩ := UnaryLambdaBodyConsumer.Bra.endpoint_chains
  exact ⟨BraSuccessfulChains.initial,BraSuccessfulChains.sourceClosed,BraSuccessfulChains.actualHistory,actual_four_step_trace,
    BraFunctionConsumer.source_matches,actual_final_matches,auxiliary,sourceChain,targetChain,oldBody,newBody,
    BraFunctionConsumer.source_matches.base_source_edge_fragment BraSuccessfulChains.targetClosed otherOccurrence,
    actual_final_matches.base_source_edge_fragment BraSuccessfulChains.targetClosed otherOccurrence,
    by decide,actual_mixed_terminal_pair⟩

#print axioms actual_reachable_mixed_terminal_supply
#print axioms actual_kept_lambda_finish
#print axioms actual_mixed_terminal_pair
end Lamping.Checks.UnaryMixedAppTerminalConsumer.Bra
