import Lamping.Lamping.UnaryMixedLambdaTerminalSeparation
import Lamping.Checks.UnaryLambdaBodyConsumer
set_option maxHeartbeats 4000000
namespace Lamping.Checks.UnaryMixedLambdaTerminalConsumer.Cro
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable
open UnaryBindingReachable.Cro
abbrev contextEdge := UnaryLambdaContextConsumer.Cro.edge
abbrev bindingEdge := UnaryBindingConsumer.Cro.edge
abbrev bodyEdge := UnaryLambdaBodyConsumer.Cro.edge

theorem actual_context_vs_kept
    (source : SourceEdgeFragment current croLambda.site.net (.inl ()) contextEdge [.fn])
    (target : SourceEdgeFragment current croLambda.site.reduce (.inl ()) contextEdge [.fn])
    (otherSource : SourceEdgeFragment current croLambda.site.net (.inl ()) bodyEdge [.fn,.body])
    (otherTarget : SourceEdgeFragment current croLambda.site.reduce (.inl ()) bodyEdge [.fn,.body]) :
    source.segments≠otherSource.segments ∧target.segments≠otherTarget.segments ∧
      (target.segments=otherTarget.segments ↔source.segments=otherSource.segments) := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  obtain ⟨principal⟩ := croLambda.site.actionPrincipal_exists
  obtain ⟨port,finish⟩ := UnaryLambdaBodyConsumer.Cro.actual_kept_app_finish otherTarget
  exact source.cro_copied_lambda_context_terminal_vs_kept_terminal croLambda.site
    (croLambda.sourceIso.flowBalance flow) (.inl ()) rfl source_matches principal
    target otherSource otherTarget (UnaryLambdaContextConsumer.Cro.actual_context_finish target) port.1 port.2 finish

theorem actual_binding_vs_kept
    (source : SourceEdgeFragment current croLambda.site.net (.inl ()) bindingEdge [.fn,.body,.fn])
    (target : SourceEdgeFragment current croLambda.site.reduce (.inl ()) bindingEdge [.fn,.body,.fn])
    (otherSource : SourceEdgeFragment current croLambda.site.net (.inl ()) bodyEdge [.fn,.body])
    (otherTarget : SourceEdgeFragment current croLambda.site.reduce (.inl ()) bodyEdge [.fn,.body]) :
    source.segments≠otherSource.segments ∧target.segments≠otherTarget.segments ∧
      (target.segments=otherTarget.segments ↔source.segments=otherSource.segments) := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  obtain ⟨principal⟩ := croLambda.site.actionPrincipal_exists
  obtain ⟨port,finish⟩ := UnaryLambdaBodyConsumer.Cro.actual_kept_app_finish otherTarget
  exact source.cro_copied_lambda_binding_terminal_vs_kept_terminal croLambda.site
    (croLambda.sourceIso.flowBalance flow) (.inl ()) rfl source_matches principal
    target otherSource otherTarget (actual_variable_finish target.access target.word) port.1 port.2 finish

theorem actual_context_vs_binding
    (source : SourceEdgeFragment current croLambda.site.net (.inl ()) contextEdge [.fn])
    (target : SourceEdgeFragment current croLambda.site.reduce (.inl ()) contextEdge [.fn])
    (otherSource : SourceEdgeFragment current croLambda.site.net (.inl ()) bindingEdge [.fn,.body,.fn])
    (otherTarget : SourceEdgeFragment current croLambda.site.reduce (.inl ()) bindingEdge [.fn,.body,.fn]) :
    source.segments≠otherSource.segments ∧target.segments≠otherTarget.segments ∧
      (target.segments=otherTarget.segments ↔source.segments=otherSource.segments) := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  obtain ⟨principal⟩ := croLambda.site.actionPrincipal_exists
  exact source.cro_copied_lambda_context_vs_binding croLambda.site
    (croLambda.sourceIso.flowBalance flow) (.inl ()) rfl source_matches principal
    target otherSource otherTarget (UnaryLambdaContextConsumer.Cro.actual_context_finish target)
    (actual_variable_finish otherTarget.access otherTarget.word)

/-- The closed two-step fixture supplies all three distinct occurrences and
successful endpoint chains; the auxiliary BODY edge is not a reading edge. -/
theorem actual_reachable_terminal_supply :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet croLambda.site.reduce)
      [.beta 0,.croAction .lam 0 1 (by decide)] ∧
    Matches croLambda.site.net (.inl ()) current.erase ∧Matches croLambda.site.reduce (.inl ()) current.erase ∧
    AuxiliaryAt current [.fn,.body] ∧
    PrerequisiteChain current [.fn] [[.fn]] ∧
    PrerequisiteChain current [.fn,.body] WrappedSuccessfulChains.bodyEdges ∧
    EndpointChain current (SyntaxIncidence.source current UnaryLambdaBodyConsumer.Cro.bodyEdge) [[.fn]] ∧
    EndpointChain current (SyntaxIncidence.target current WrappedSuccessfulChains.targetClosed UnaryLambdaBodyConsumer.Cro.bodyEdge) WrappedSuccessfulChains.bodyEdges ∧
    Nonempty (SourceEdgeFragment current croLambda.site.net (.inl ()) contextEdge [.fn]) ∧
    Nonempty (SourceEdgeFragment current croLambda.site.reduce (.inl ()) contextEdge [.fn]) ∧
    Nonempty (SourceEdgeFragment current croLambda.site.net (.inl ()) bindingEdge [.fn,.body,.fn]) ∧
    Nonempty (SourceEdgeFragment current croLambda.site.reduce (.inl ()) bindingEdge [.fn,.body,.fn]) ∧
    Nonempty (SourceEdgeFragment current croLambda.site.net (.inl ()) bodyEdge [.fn,.body]) ∧
    Nonempty (SourceEdgeFragment current croLambda.site.reduce (.inl ()) bodyEdge [.fn,.body]) := by
  obtain ⟨oldContext,newContext,contextChain⟩ := UnaryLambdaContextConsumer.Cro.actual_fragments_and_chain
  obtain ⟨oldBinding,newBinding,bindingChain⟩ := UnaryBindingConsumer.Cro.actual_fragments_and_successful_chain
  obtain ⟨oldBody,newBody⟩ := UnaryLambdaBodyConsumer.Cro.actual_fragments
  obtain ⟨sourceChain,targetChain⟩ := UnaryLambdaBodyConsumer.Cro.endpoint_chains
  exact ⟨WrappedSuccessfulChains.initial,WrappedSuccessfulChains.sourceClosed,WrappedSuccessfulChains.actualHistory,
    UnaryBindingConsumer.Cro.actual_two_rule_trace,source_matches,target_matches,
    UnaryLambdaBodyConsumer.Cro.auxiliary,contextChain,bindingChain,sourceChain,targetChain,
    oldContext,newContext,oldBinding,newBinding,oldBody,newBody⟩

#print axioms actual_reachable_terminal_supply
#print axioms actual_context_vs_kept
#print axioms actual_binding_vs_kept
#print axioms actual_context_vs_binding
end Lamping.Checks.UnaryMixedLambdaTerminalConsumer.Cro
namespace Lamping.Checks.UnaryMixedLambdaTerminalConsumer.Bra
open AG Graph Lambda Lambda.Labelled BraFunctionReachable
open UnaryBindingReachable.Bra
abbrev contextEdge := UnaryLambdaContextConsumer.Bra.edge
abbrev bindingEdge := UnaryBindingConsumer.Bra.edge
abbrev bodyEdge := UnaryLambdaBodyConsumer.Bra.edge

theorem actual_context_vs_kept
    (source : SourceEdgeFragment current braLambda.site.net (.inl ()) contextEdge [.arg])
    (target : SourceEdgeFragment current braLambda.site.reduce (.inl ()) contextEdge [.arg])
    (otherSource : SourceEdgeFragment current braLambda.site.net (.inl ()) bodyEdge [.arg,.body])
    (otherTarget : SourceEdgeFragment current braLambda.site.reduce (.inl ()) bodyEdge [.arg,.body]) :
    source.segments≠otherSource.segments ∧target.segments≠otherTarget.segments ∧
      (target.segments=otherTarget.segments ↔source.segments=otherSource.segments) := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  obtain ⟨principal⟩ := braLambda.site.actionPrincipal_exists
  obtain ⟨port,finish⟩ := UnaryLambdaBodyConsumer.Bra.actual_kept_app_finish otherTarget
  exact source.bra_copied_lambda_context_terminal_vs_kept_terminal braLambda.site
    (braLambda.sourceIso.flowBalance flow) (.inl ()) rfl source_matches principal
    target otherSource otherTarget (UnaryLambdaContextConsumer.Bra.actual_context_finish target) port.1 port.2 finish

theorem actual_binding_vs_kept
    (source : SourceEdgeFragment current braLambda.site.net (.inl ()) bindingEdge [.arg,.body,.fn])
    (target : SourceEdgeFragment current braLambda.site.reduce (.inl ()) bindingEdge [.arg,.body,.fn])
    (otherSource : SourceEdgeFragment current braLambda.site.net (.inl ()) bodyEdge [.arg,.body])
    (otherTarget : SourceEdgeFragment current braLambda.site.reduce (.inl ()) bodyEdge [.arg,.body]) :
    source.segments≠otherSource.segments ∧target.segments≠otherTarget.segments ∧
      (target.segments=otherTarget.segments ↔source.segments=otherSource.segments) := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  obtain ⟨principal⟩ := braLambda.site.actionPrincipal_exists
  obtain ⟨port,finish⟩ := UnaryLambdaBodyConsumer.Bra.actual_kept_app_finish otherTarget
  exact source.bra_copied_lambda_binding_terminal_vs_kept_terminal braLambda.site
    (braLambda.sourceIso.flowBalance flow) (.inl ()) rfl source_matches principal
    target otherSource otherTarget (actual_variable_finish target.access target.word) port.1 port.2 finish

theorem actual_context_vs_binding
    (source : SourceEdgeFragment current braLambda.site.net (.inl ()) contextEdge [.arg])
    (target : SourceEdgeFragment current braLambda.site.reduce (.inl ()) contextEdge [.arg])
    (otherSource : SourceEdgeFragment current braLambda.site.net (.inl ()) bindingEdge [.arg,.body,.fn])
    (otherTarget : SourceEdgeFragment current braLambda.site.reduce (.inl ()) bindingEdge [.arg,.body,.fn]) :
    source.segments≠otherSource.segments ∧target.segments≠otherTarget.segments ∧
      (target.segments=otherTarget.segments ↔source.segments=otherSource.segments) := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  obtain ⟨principal⟩ := braLambda.site.actionPrincipal_exists
  exact source.bra_copied_lambda_context_vs_binding braLambda.site
    (braLambda.sourceIso.flowBalance flow) (.inl ()) rfl source_matches principal
    target otherSource otherTarget (UnaryLambdaContextConsumer.Bra.actual_context_finish target)
    (actual_variable_finish otherTarget.access otherTarget.word)

/-- The closed two-step fixture supplies all three distinct occurrences and
successful endpoint chains; the auxiliary BODY edge is not a reading edge. -/
theorem actual_reachable_terminal_supply :
    INIT original ∧Closed original.erase ∧History [[]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet braLambda.site.reduce)
      [.beta 0,.braAction .lam 0 1 (by decide)] ∧
    Matches braLambda.site.net (.inl ()) current.erase ∧Matches braLambda.site.reduce (.inl ()) current.erase ∧
    AuxiliaryAt current [.arg,.body] ∧
    PrerequisiteChain current [.arg] [[.arg],[.fn]] ∧
    PrerequisiteChain current [.arg,.body] BraSuccessfulChains.bodyEdges ∧
    EndpointChain current (SyntaxIncidence.source current UnaryLambdaBodyConsumer.Bra.bodyEdge) [[.arg],[.fn]] ∧
    EndpointChain current (SyntaxIncidence.target current BraSuccessfulChains.targetClosed UnaryLambdaBodyConsumer.Bra.bodyEdge) BraSuccessfulChains.bodyEdges ∧
    Nonempty (SourceEdgeFragment current braLambda.site.net (.inl ()) contextEdge [.arg]) ∧
    Nonempty (SourceEdgeFragment current braLambda.site.reduce (.inl ()) contextEdge [.arg]) ∧
    Nonempty (SourceEdgeFragment current braLambda.site.net (.inl ()) bindingEdge [.arg,.body,.fn]) ∧
    Nonempty (SourceEdgeFragment current braLambda.site.reduce (.inl ()) bindingEdge [.arg,.body,.fn]) ∧
    Nonempty (SourceEdgeFragment current braLambda.site.net (.inl ()) bodyEdge [.arg,.body]) ∧
    Nonempty (SourceEdgeFragment current braLambda.site.reduce (.inl ()) bodyEdge [.arg,.body]) := by
  obtain ⟨oldContext,newContext,contextChain⟩ := UnaryLambdaContextConsumer.Bra.actual_fragments_and_chain
  obtain ⟨oldBinding,newBinding,bindingChain⟩ := UnaryBindingConsumer.Bra.actual_fragments_and_successful_chain
  obtain ⟨oldBody,newBody⟩ := UnaryLambdaBodyConsumer.Bra.actual_fragments
  obtain ⟨sourceChain,targetChain⟩ := UnaryLambdaBodyConsumer.Bra.endpoint_chains
  exact ⟨BraSuccessfulChains.initial,BraSuccessfulChains.sourceClosed,BraSuccessfulChains.actualHistory,
    UnaryBindingConsumer.Bra.actual_two_rule_trace,source_matches,target_matches,
    UnaryLambdaBodyConsumer.Bra.auxiliary,contextChain,bindingChain,sourceChain,targetChain,
    oldContext,newContext,oldBinding,newBinding,oldBody,newBody⟩

#print axioms actual_reachable_terminal_supply
#print axioms actual_context_vs_kept
#print axioms actual_binding_vs_kept
#print axioms actual_context_vs_binding
end Lamping.Checks.UnaryMixedLambdaTerminalConsumer.Bra