import Lamping.Lamping.UnaryMixedAppParentSeparation
import Lamping.Checks.FunctionWrappedMixedConsumer
set_option maxHeartbeats 4000000
namespace Lamping.Checks.UnaryMixedAppParentConsumer
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable
open FunctionWrappedConsumer FunctionWrappedMixedConsumer WrappedLambdaParent

/-- Different actual syntax occurrences, not two choices at one occurrence.
The generic theorem itself has no restriction on the child terminals. -/
theorem actual_four_choices_comparison
    (sourceRoot : SourceEdgeFragment current croApp.site.net (.inl ()) rootEdge [.fn])
    (sourceBody : SourceEdgeFragment current croApp.site.net (.inl ()) edge [.fn,.body,.fn])
    (targetRoot : SourceEdgeFragment current croApp.site.reduce (.inl ()) rootEdge [.fn])
    (targetBody : SourceEdgeFragment current croApp.site.reduce (.inl ()) edge [.fn,.body,.fn]) :
    sourceBody.segments≠sourceRoot.segments ∧targetBody.segments≠targetRoot.segments ∧
      (targetBody.segments=targetRoot.segments ↔sourceBody.segments=sourceRoot.segments) := by
  obtain ⟨flow,_,_,_,_⟩ := cro_certified
  obtain ⟨principal⟩ := croApp.site.actionPrincipal_exists
  obtain ⟨oldParent,oldWord,_⟩ := Matches.observation croApp.site.net source_matches
    (⟨[.fn,.body],rfl⟩ : Position current.erase)
  have sourceWord : [.fn,.body,.fn]=accessWord croApp.site.net oldParent.val++[.fn] := by
    rw [oldWord];rfl
  have targetWord : [.fn,.body,.fn]=accessWord croApp.site.reduce appParent.val++[.fn] := by
    change _=accessWord croApp.site.reduce appParentEdges++[.fn]
    rw [appParentWord];rfl
  exact sourceBody.cro_copied_app_parent_vs_kept_parent croApp.site
    (croApp.sourceIso.flowBalance flow) (.inl ()) rfl source_matches actual_final_matches principal
    targetBody sourceRoot targetRoot role rootRole oldParent appParent
    WrappedOuterParent.sourceParent WrappedOuterParent.targetParent sourceWord targetWord
    (by rw [WrappedOuterParent.sourceWord];rfl) (by rw [WrappedOuterParent.targetWord];rfl)
    appParentFinish outerKept4 appCtx WrappedOuterParent.targetFinish

theorem actual_reachable_distinct_parent_comparison :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet croApp.site.reduce)
      [.beta 0,.croAction .lam 0 1 (by decide),.croAction .cro 0 1 (by decide),.croAction .app 0 1 (by decide)] ∧
    Matches croApp.site.net (.inl ()) current.erase ∧Matches croApp.site.reduce (.inl ()) current.erase ∧
    Nonempty (SourceEdgeFragment current croApp.site.net (.inl ()) rootEdge [.fn]) ∧
    Nonempty (SourceEdgeFragment current croApp.site.reduce (.inl ()) rootEdge [.fn]) ∧
    Nonempty (SourceEdgeFragment current croApp.site.net (.inl ()) edge [.fn,.body,.fn]) ∧
    Nonempty (SourceEdgeFragment current croApp.site.reduce (.inl ()) edge [.fn,.body,.fn]) ∧
    PrerequisiteChain current [] WrappedSuccessfulChains.rootEdges ∧
    PrerequisiteChain current [.fn,.body] WrappedSuccessfulChains.bodyEdges ∧
    ∀ (sourceRoot : SourceEdgeFragment current croApp.site.net (.inl ()) rootEdge [.fn])
      (sourceBody : SourceEdgeFragment current croApp.site.net (.inl ()) edge [.fn,.body,.fn])
      (targetRoot : SourceEdgeFragment current croApp.site.reduce (.inl ()) rootEdge [.fn])
      (targetBody : SourceEdgeFragment current croApp.site.reduce (.inl ()) edge [.fn,.body,.fn]),
      sourceBody.segments≠sourceRoot.segments ∧targetBody.segments≠targetRoot.segments ∧
        (targetBody.segments=targetRoot.segments ↔sourceBody.segments=sourceRoot.segments) := by
  obtain ⟨sr,tr,sb,tb,rootChain,bodyChain⟩ := actual_mixed_supply
  exact ⟨WrappedSuccessfulChains.initial,WrappedSuccessfulChains.sourceClosed,WrappedSuccessfulChains.actualHistory,
    actual_four_step_trace,source_matches,actual_final_matches,sr,tr,sb,tb,rootChain,bodyChain,actual_four_choices_comparison⟩

#print axioms actual_four_choices_comparison
#print axioms actual_reachable_distinct_parent_comparison
end Lamping.Checks.UnaryMixedAppParentConsumer
