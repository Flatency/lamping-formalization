import Lamping.Checks.FunctionWrappedBindingFinish
import Lamping.Checks.WrappedLambdaParent
import Lamping.Lamping.ActionCopiedFunctionComparison

set_option maxHeartbeats 4000000
namespace Lamping.Checks.FunctionWrappedConsumer
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable FunctionWrappedBodyParent
open WrappedLambdaParent FunctionWrappedBindingFinish

noncomputable def appParentEdges : List (Endpoint finalNet) := finalEdges++bodyEdges
theorem appParentLabels (a : Context) : Labelling finalNet appParentEdges a a :=
  (finalLabels a).append_seam (bodyLabels a) (by
    intro e f last first
    have he:=Option.some.inj (last.symm.trans finalFinish)
    have hf:=Option.some.inj (first.symm.trans bodyHead)
    subst e;subst f
    rw [Pairing.involutive]
    exact LabelledTurn.node (g:=finalNet) finalLambda _ _ (.direct (.lamBody a)))
theorem appParentWord : accessWord finalNet appParentEdges=[.fn,.body] := by
  rw [appParentEdges,accessWord_append finalNet _ _ (finalLabels Context.empty).nonempty]
  change accessWord finalNet finalEdges++bodyEdges.flatMap (arrivalWord finalNet)=_
  rw [finalWord,bodyWord];rfl
theorem appParentFinish : appParentEdges.getLast?=
    some (finalNet.wire (.inl ⟨.inr (.inl ()),appCtx⟩)) := by
  rw [appParentEdges,List.getLast?_append,bodyFinish]
  rfl
noncomputable def appParent : RootAccess finalNet (.inl ()) := by
  let flow := Classical.choose app_certified
  exact ⟨appParentEdges,⟨⟨⟨Context.empty,Context.empty,appParentLabels _⟩,
    (appParentLabels Context.empty).root_forward_of_flow flow (.inl ()) rfl rfl⟩,
    rfl,⟨.app,by
      unfold accessKind;rw [appParentFinish]
      simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩⟩

abbrev bodyTerm : LTerm := .app (.atom 5) (.var (.atom 6) 0) (.lam (.atom 7) (.var (.atom 8) 0))
abbrev leafTerm : LTerm := .var (.atom 6) 0
abbrev env : List Label := [WrappedSuccessfulChains.functionLabel]
abbrev edge := sourceEdge env (.appFn (.atom 5)) leafTerm
def occurrence : SourceSubterm [] .external current [.fn,.body,.fn] env (.appFn (.atom 5)) leafTerm :=
  .fn (.body (.fn .nil))
theorem role : SourceDeparture bodyTerm .fn edge.fromPort := .fn
theorem source_matches : Matches croApp.site.net (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := cro_certified
  exact croApp.sourceIso.matches matching

theorem actual_function_pair_equality
    (sourceLeft sourceRight : SourceEdgeFragment current croApp.site.net (.inl ()) edge [.fn,.body,.fn])
    (targetLeft targetRight : SourceEdgeFragment current finalNet (.inl ()) edge [.fn,.body,.fn]) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨flow,_,_,_,_⟩ := cro_certified
  have actualFlow := croApp.sourceIso.flowBalance flow
  obtain ⟨principal⟩ := croApp.site.actionPrincipal_exists
  let parentPosition : Position current.erase := ⟨[.fn,.body],rfl⟩
  obtain ⟨oldParent,oldWord,_⟩ := Matches.observation croApp.site.net source_matches parentPosition
  have targetWord : [.fn,.body,.fn]=accessWord finalNet appParent.val++[.fn] := by
    change _=accessWord finalNet appParentEdges++[.fn]
    rw [appParentWord];rfl
  have sourceWord : [.fn,.body,.fn]=accessWord croApp.site.net oldParent.val++[.fn] := by
    rw [oldWord];rfl
  have leftEnd := variable_finish finalParent finalWord finalFinish targetLeft.access targetLeft.word
  have rightEnd := variable_finish finalParent finalWord finalFinish targetRight.access targetRight.word
  exact sourceLeft.cro_copied_function_kept_equality croApp.site actualFlow (.inl ()) rfl
    source_matches actual_final_matches principal targetLeft sourceRight targetRight role role
    oldParent oldParent appParent appParent sourceWord sourceWord targetWord targetWord
    appParentFinish appParentFinish copiedLambda4 copiedLambda4 lamBind lamBind leftEnd rightEnd

theorem actual_fragments_and_successful_chain :
    Nonempty (SourceEdgeFragment current croApp.site.net (.inl ()) edge [.fn,.body,.fn]) ∧
    Nonempty (SourceEdgeFragment current finalNet (.inl ()) edge [.fn,.body,.fn]) ∧
    PrerequisiteChain current [.fn,.body] [[.fn,.body,.fn],[.fn]] :=
  ⟨source_matches.base_source_edge_fragment WrappedSuccessfulChains.targetClosed occurrence,
    actual_final_matches.base_source_edge_fragment WrappedSuccessfulChains.targetClosed occurrence,
    WrappedSuccessfulChains.body_chain⟩

/-- A single actual closed-encoding instance supplies all semantic and
physical premises of the successful copied-FUNCTION comparison. -/
theorem actual_reachable_function_comparison :
    INIT original ∧ Closed original.erase ∧ History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet finalNet)
      [.beta 0,.croAction .lam 0 1 (by decide),.croAction .cro 0 1 (by decide),.croAction .app 0 1 (by decide)] ∧
    Matches croApp.site.net (.inl ()) current.erase ∧ Matches finalNet (.inl ()) current.erase ∧
    Nonempty (SourceEdgeFragment current croApp.site.net (.inl ()) edge [.fn,.body,.fn]) ∧
    Nonempty (SourceEdgeFragment current finalNet (.inl ()) edge [.fn,.body,.fn]) ∧
    PrerequisiteChain current [.fn,.body] [[.fn,.body,.fn],[.fn]] ∧
    ∀ (sourceLeft sourceRight : SourceEdgeFragment current croApp.site.net (.inl ()) edge [.fn,.body,.fn])
      (targetLeft targetRight : SourceEdgeFragment current finalNet (.inl ()) edge [.fn,.body,.fn]),
      targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨sourceExists,targetExists,chain⟩ := actual_fragments_and_successful_chain
  exact ⟨WrappedSuccessfulChains.initial,WrappedSuccessfulChains.sourceClosed,
    WrappedSuccessfulChains.actualHistory,actual_four_step_trace,source_matches,actual_final_matches,
    sourceExists,targetExists,chain,actual_function_pair_equality⟩
#print axioms appParent
#print axioms actual_function_pair_equality
#print axioms actual_fragments_and_successful_chain
#print axioms actual_reachable_function_comparison
end Lamping.Checks.FunctionWrappedConsumer
