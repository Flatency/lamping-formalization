import Lamping.Checks.FunctionWrappedConsumer
import Lamping.Checks.WrappedOuterParent
import Lamping.Lamping.FragmentParentSeparation
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FunctionWrappedMixedConsumer
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable FunctionWrappedBodyParent
open FunctionWrappedConsumer WrappedLambdaParent

abbrev rootFunction : LTerm := .lam WrappedSuccessfulChains.functionLabel bodyTerm
abbrev rootEdge := sourceEdge [] (.appFn (.atom 0)) rootFunction
def rootOccurrence : SourceSubterm [] .external current [.fn] [] (.appFn (.atom 0)) rootFunction := .fn .nil
theorem rootRole : SourceDeparture current .fn rootEdge.fromPort := .fn

theorem source_body_head
    (source : SourceEdgeFragment current croApp.site.net (.inl ()) edge [.fn,.body,.fn])
    (target : SourceEdgeFragment current finalNet (.inl ()) edge [.fn,.body,.fn]) :
    source.segments.head?=some (.inl ⟨.inr (.inr ()),.inl ()⟩) := by
  obtain ⟨flow,_,_,_,_⟩ := cro_certified
  obtain ⟨principal⟩ := croApp.site.actionPrincipal_exists
  obtain ⟨oldParent,oldWord,_⟩ := Matches.observation croApp.site.net source_matches
    (⟨[.fn,.body],rfl⟩ : Position current.erase)
  have sourceWord : [.fn,.body,.fn]=accessWord croApp.site.net oldParent.val++[.fn] := by rw [oldWord];rfl
  have targetWord : [.fn,.body,.fn]=accessWord finalNet appParent.val++[.fn] := by
    change _=accessWord finalNet appParentEdges++[.fn]
    rw [appParentWord];rfl
  obtain ⟨a,b,labels⟩ := target.access.property.1.1
  have terminal := FunctionWrappedBindingFinish.variable_finish finalParent finalWord finalFinish
    target.access target.word
  obtain ⟨rawTail,oldTail,seam,_targetShape,sourceShape,_relation,_pieceLabels⟩ :=
    source.cro_copied_function_kept_cut croApp.site (croApp.sourceIso.flowBalance flow) (.inl ()) rfl
      source_matches actual_final_matches principal target role oldParent appParent sourceWord targetWord
      appParentFinish copiedLambda4 lamBind terminal labels
  have reverseHead : (reverseEdges principal.edges).head?=
      some (.inl ⟨.inr (.inr ()),.inl ()⟩ : Endpoint croApp.site.net) := by
    simp only [reverseEdges,List.head?_map,List.head?_reverse,principal.last,Option.map_some,Pairing.involutive]
  obtain ⟨tail,reverseSplit⟩ := List.head?_eq_some_iff.mp reverseHead
  rw [sourceShape,reverseSplit]
  rfl

theorem actual_source_mixed_different
    (rootFragment : SourceEdgeFragment current croApp.site.net (.inl ()) rootEdge [.fn])
    (bodyFragment : SourceEdgeFragment current croApp.site.net (.inl ()) edge [.fn,.body,.fn])
    (bodyTarget : SourceEdgeFragment current finalNet (.inl ()) edge [.fn,.body,.fn]) :
    rootFragment.segments≠bodyFragment.segments := by
  obtain ⟨departure,rootHead⟩ := rootFragment.head_node_of_parent source_matches rootRole
    WrappedOuterParent.sourceParent (by rw [WrappedOuterParent.sourceWord];rfl)
    (.inl outerKept4) appCtx WrappedOuterParent.sourceFinish
  have bodyHead := source_body_head bodyFragment bodyTarget
  intro same
  have heads:=congrArg List.head? same
  rw [rootHead,bodyHead] at heads
  have nodes:=congrArg Sigma.fst (Sum.inl.inj (Option.some.inj heads))
  cases nodes

theorem actual_target_mixed_different
    (rootFragment : SourceEdgeFragment current finalNet (.inl ()) rootEdge [.fn])
    (bodyFragment : SourceEdgeFragment current finalNet (.inl ()) edge [.fn,.body,.fn]) :
    rootFragment.segments≠bodyFragment.segments := by
  exact rootFragment.ne_of_parent_nodes actual_final_matches bodyFragment rootRole role
    WrappedOuterParent.targetParent appParent
    (by rw [WrappedOuterParent.targetWord];rfl)
    (by change _=accessWord finalNet appParentEdges++[.fn];rw [appParentWord];rfl)
    (.inl outerKept4) (.inr (.inl ())) appCtx appCtx
    WrappedOuterParent.targetFinish appParentFinish (by intro h;cases h)

theorem actual_mixed_function_comparison
    (sourceRoot : SourceEdgeFragment current croApp.site.net (.inl ()) rootEdge [.fn])
    (sourceBody : SourceEdgeFragment current croApp.site.net (.inl ()) edge [.fn,.body,.fn])
    (targetRoot : SourceEdgeFragment current finalNet (.inl ()) rootEdge [.fn])
    (targetBody : SourceEdgeFragment current finalNet (.inl ()) edge [.fn,.body,.fn]) :
    sourceRoot.segments≠sourceBody.segments ∧ targetRoot.segments≠targetBody.segments ∧
    (targetRoot.segments=targetBody.segments ↔sourceRoot.segments=sourceBody.segments) := by
  have sourceNe:=actual_source_mixed_different sourceRoot sourceBody targetBody
  have targetNe:=actual_target_mixed_different targetRoot targetBody
  exact ⟨sourceNe,targetNe,⟨fun h=>False.elim (targetNe h),fun h=>False.elim (sourceNe h)⟩⟩

theorem actual_mixed_supply :
    Nonempty (SourceEdgeFragment current croApp.site.net (.inl ()) rootEdge [.fn]) ∧
    Nonempty (SourceEdgeFragment current finalNet (.inl ()) rootEdge [.fn]) ∧
    Nonempty (SourceEdgeFragment current croApp.site.net (.inl ()) edge [.fn,.body,.fn]) ∧
    Nonempty (SourceEdgeFragment current finalNet (.inl ()) edge [.fn,.body,.fn]) ∧
    PrerequisiteChain current [] [[.fn]] ∧
    PrerequisiteChain current [.fn,.body] [[.fn,.body,.fn],[.fn]] := by
  obtain ⟨oldBody,newBody,bodyChain⟩ := actual_fragments_and_successful_chain
  exact ⟨source_matches.base_source_edge_fragment WrappedSuccessfulChains.targetClosed rootOccurrence,
    actual_final_matches.base_source_edge_fragment WrappedSuccessfulChains.targetClosed rootOccurrence,
    oldBody,newBody,WrappedSuccessfulChains.root_chain,bodyChain⟩
#print axioms actual_source_mixed_different
#print axioms actual_target_mixed_different
#print axioms actual_mixed_function_comparison
#print axioms actual_mixed_supply
end Lamping.Checks.FunctionWrappedMixedConsumer
