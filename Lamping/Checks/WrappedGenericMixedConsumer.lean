import Lamping.Lamping.FanKeptFragmentComparison
import Lamping.Lamping.ActionBraCopiedFunctionComparison
import Lamping.Checks.FunctionWrappedMixedConsumer
import Lamping.Lamping.MixedFunctionParentSeparation
set_option maxHeartbeats 4000000
namespace Lamping.Checks.WrappedGenericMixedConsumer
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable FunctionWrappedBodyParent
open FunctionWrappedConsumer FunctionWrappedMixedConsumer WrappedLambdaParent

theorem actual_generic_mixed_comparison
    (sourceRoot : SourceEdgeFragment current croApp.site.net (.inl ()) rootEdge [.fn])
    (sourceBody : SourceEdgeFragment current croApp.site.net (.inl ()) edge [.fn,.body,.fn])
    (targetRoot : SourceEdgeFragment current finalNet (.inl ()) rootEdge [.fn])
    (targetBody : SourceEdgeFragment current finalNet (.inl ()) edge [.fn,.body,.fn]) :
    sourceRoot.segments≠sourceBody.segments ∧ targetRoot.segments≠targetBody.segments ∧
    (targetRoot.segments=targetBody.segments ↔sourceRoot.segments=sourceBody.segments) := by
  obtain ⟨flow,_,_,_,_⟩ := cro_certified
  obtain ⟨principal⟩ := croApp.site.actionPrincipal_exists
  obtain ⟨oldParent,oldWord,_⟩ := Matches.observation croApp.site.net source_matches
    (⟨[.fn,.body],rfl⟩ : Position current.erase)
  have sourceWord : [.fn,.body,.fn]=accessWord croApp.site.net oldParent.val++[.fn] := by rw [oldWord];rfl
  have targetWord : [.fn,.body,.fn]=accessWord finalNet appParent.val++[.fn] := by
    change _=accessWord finalNet appParentEdges++[.fn]
    rw [appParentWord];rfl
  have terminal := FunctionWrappedBindingFinish.variable_finish finalParent finalWord finalFinish
    targetBody.access targetBody.word
  exact sourceBody.cro_copied_function_vs_kept_parent croApp.site
    (croApp.sourceIso.flowBalance flow) (.inl ()) rfl source_matches actual_final_matches principal
    targetBody role oldParent appParent sourceWord targetWord appParentFinish copiedLambda4 lamBind terminal
    sourceRoot targetRoot rootRole WrappedOuterParent.sourceParent WrappedOuterParent.targetParent
    (by rw [WrappedOuterParent.sourceWord];rfl) (by rw [WrappedOuterParent.targetWord];rfl)
    outerKept4 outerKept4 appCtx appCtx WrappedOuterParent.sourceFinish WrappedOuterParent.targetFinish

#print axioms actual_generic_mixed_comparison
end Lamping.Checks.WrappedGenericMixedConsumer

#print axioms Lamping.AG.SourceEdgeFragment.bra_copied_function_kept_cut
#print axioms Lamping.AG.SourceEdgeFragment.bra_copied_function_kept_equality
#print axioms Lamping.AG.SourceEdgeFragment.cro_copied_function_vs_kept_parent
#print axioms Lamping.AG.SourceEdgeFragment.action_kept_parent_cut
#print axioms Lamping.AG.SourceEdgeFragment.fan_target_unique_of_contiguous_source
#print axioms Lamping.AG.SourceEdgeFragment.fan_target_unique_of_kept_parent_fragment
#print axioms Lamping.AG.passive_reverse_swaps
#print axioms Lamping.AG.SourceEdgeFragment.fan_kept_piece_equality
