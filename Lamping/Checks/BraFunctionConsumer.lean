import Lamping.Checks.BraFunctionBindingFinish
import Lamping.Checks.BraArgumentParent
import Lamping.Lamping.ActionBraCopiedFunctionComparison
set_option maxHeartbeats 4000000
namespace Lamping.Checks.BraFunctionConsumer
open AG Graph Lambda Lambda.Labelled BraFunctionReachable BraFunctionBodyParent
open BraArgumentParent BraFunctionBindingFinish

noncomputable def appParentEdges : List (Endpoint finalNet) := finalEdges++bodyEdges
theorem appParentLabels : Labelling finalNet appParentEdges Context.empty Context.empty := by
  have tailLabels : Labelling finalNet bodyEdges Context.empty Context.empty := by
    simpa only [Context.cons_empty] using bodyLabels Context.empty .empty .empty
  exact finalLabels.append_seam tailLabels (by
    intro e f last first
    have he:=Option.some.inj (last.symm.trans finalFinish)
    have hf:=Option.some.inj (first.symm.trans bodyHead)
    subst e;subst f
    rw [Pairing.involutive]
    exact LabelledTurn.node (g:=finalNet) finalLambda _ _ (.direct (.lamBody Context.empty)))
theorem appParentWord : accessWord finalNet appParentEdges=[.arg,.body] := by
  rw [appParentEdges,accessWord_append finalNet _ _ finalLabels.nonempty]
  change accessWord finalNet finalEdges++bodyEdges.flatMap (arrivalWord finalNet)=_
  rw [finalWord,bodyWord];rfl
theorem appParentFinish : appParentEdges.getLast?=
    some (finalNet.wire (.inl ⟨.inr (.inl ()),appCtx⟩)) := by
  rw [appParentEdges,List.getLast?_append,bodyFinish]
  rfl
noncomputable def appParent : RootAccess finalNet (.inl ()) := by
  let flow := Classical.choose app_certified
  exact ⟨appParentEdges,⟨⟨⟨Context.empty,Context.empty,appParentLabels⟩,
    appParentLabels.root_forward_of_flow flow (.inl ()) rfl rfl⟩,
    rfl,⟨.app,by
      unfold accessKind;rw [appParentFinish]
      simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩⟩

abbrev bodyTerm : LTerm := .app (.atom 7) (.var (.atom 8) 0) (.lam (.atom 9) (.var (.atom 10) 0))
abbrev leafTerm : LTerm := .var (.atom 8) 0
abbrev env : List Label := [BraSuccessfulChains.argumentLabel]
abbrev edge := sourceEdge env (.appFn (.atom 7)) leafTerm
def occurrence : SourceSubterm [] .external current [.arg,.body,.fn] env (.appFn (.atom 7)) leafTerm :=
  .arg (.body (.fn .nil))
theorem role : SourceDeparture bodyTerm .fn edge.fromPort := .fn
theorem source_matches : Matches braApp.site.net (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := cro_certified
  exact braApp.sourceIso.matches matching

theorem actual_function_pair_equality
    (sourceLeft sourceRight : SourceEdgeFragment current braApp.site.net (.inl ()) edge [.arg,.body,.fn])
    (targetLeft targetRight : SourceEdgeFragment current finalNet (.inl ()) edge [.arg,.body,.fn]) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨flow,_,_,_,_⟩ := cro_certified
  have actualFlow := braApp.sourceIso.flowBalance flow
  obtain ⟨principal⟩ := braApp.site.actionPrincipal_exists
  obtain ⟨oldParent,oldWord,_⟩ := Matches.observation braApp.site.net source_matches
    (⟨[.arg,.body],rfl⟩ : Position current.erase)
  have targetWord : [.arg,.body,.fn]=accessWord finalNet appParent.val++[.fn] := by
    change _=accessWord finalNet appParentEdges++[.fn]
    rw [appParentWord];rfl
  have sourceWord : [.arg,.body,.fn]=accessWord braApp.site.net oldParent.val++[.fn] := by
    rw [oldWord];rfl
  have leftEnd := variable_finish finalParent finalWord finalFinish targetLeft.access targetLeft.word
  have rightEnd := variable_finish finalParent finalWord finalFinish targetRight.access targetRight.word
  exact sourceLeft.bra_copied_function_kept_equality braApp.site actualFlow (.inl ()) rfl
    source_matches actual_final_matches principal targetLeft sourceRight targetRight role role
    oldParent oldParent appParent appParent sourceWord sourceWord targetWord targetWord
    appParentFinish appParentFinish copiedLambda4 copiedLambda4 lamBind lamBind leftEnd rightEnd

theorem actual_fragments_and_successful_chain :
    Nonempty (SourceEdgeFragment current braApp.site.net (.inl ()) edge [.arg,.body,.fn]) ∧
    Nonempty (SourceEdgeFragment current finalNet (.inl ()) edge [.arg,.body,.fn]) ∧
    PrerequisiteChain current [.arg,.body] [[.arg,.body,.fn],[.arg],[.fn]] :=
  ⟨source_matches.base_source_edge_fragment BraSuccessfulChains.targetClosed occurrence,
    actual_final_matches.base_source_edge_fragment BraSuccessfulChains.targetClosed occurrence,
    BraSuccessfulChains.body_chain⟩

theorem actual_reachable_function_comparison :
    INIT original ∧ Closed original.erase ∧ History [[]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet finalNet)
      [.beta 0,.braAction .lam 0 1 (by decide),.braAction .cro 0 1 (by decide),.braAction .app 0 1 (by decide)] ∧
    Matches braApp.site.net (.inl ()) current.erase ∧ Matches finalNet (.inl ()) current.erase ∧
    Nonempty (SourceEdgeFragment current braApp.site.net (.inl ()) edge [.arg,.body,.fn]) ∧
    Nonempty (SourceEdgeFragment current finalNet (.inl ()) edge [.arg,.body,.fn]) ∧
    PrerequisiteChain current [.arg,.body] [[.arg,.body,.fn],[.arg],[.fn]] ∧
    ∀ (sourceLeft sourceRight : SourceEdgeFragment current braApp.site.net (.inl ()) edge [.arg,.body,.fn])
      (targetLeft targetRight : SourceEdgeFragment current finalNet (.inl ()) edge [.arg,.body,.fn]),
      targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨sourceExists,targetExists,chain⟩ := actual_fragments_and_successful_chain
  exact ⟨BraSuccessfulChains.initial,BraSuccessfulChains.sourceClosed,
    BraSuccessfulChains.actualHistory,actual_four_step_trace,source_matches,actual_final_matches,
    sourceExists,targetExists,chain,actual_function_pair_equality⟩
#print axioms appParent
#print axioms actual_function_pair_equality
#print axioms actual_fragments_and_successful_chain
#print axioms actual_reachable_function_comparison
end Lamping.Checks.BraFunctionConsumer
