import Lamping.Lamping.ActionCopiedAppContextComparison
import Lamping.Checks.FunctionWrappedConsumer
import Lamping.Checks.BraFunctionConsumer
import Lamping.Checks.UnaryLambdaBodyConsumer
set_option maxHeartbeats 4000000
namespace Lamping.Checks.UnaryAppContextConsumer
namespace Cro
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable
abbrev position : Path := UnaryLambdaBodyConsumer.Cro.position
abbrev edge := UnaryLambdaBodyConsumer.Cro.edge
abbrev bodyEdge : SyntaxIncidence.Edge current := UnaryLambdaBodyConsumer.Cro.bodyEdge

def occurrence := UnaryLambdaBodyConsumer.Cro.occurrence
theorem role : SourceDeparture UnaryLambdaBodyConsumer.Cro.lambdaTerm .body edge.fromPort :=
  UnaryLambdaBodyConsumer.Cro.role

theorem auxiliary : AuxiliaryAt current position := UnaryLambdaBodyConsumer.Cro.auxiliary
theorem never_reading_member (chain : PrerequisiteChain current p es) : position∉es :=
  UnaryLambdaBodyConsumer.Cro.never_reading_member chain

theorem actual_copied_app_finish
    (fragment : SourceEdgeFragment current croApp.site.reduce (.inl ()) edge position) :
    fragment.access.val.getLast?=some (croApp.site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)) := by
  have same : FunctionWrappedConsumer.appParent=fragment.access :=
    actual_final_matches.accessWord_injective (FunctionWrappedConsumer.appParentWord.trans fragment.word.symm)
  rw [←same]
  exact FunctionWrappedConsumer.appParentFinish

theorem actual_body_reader_pair
    (sourceFirst sourceSecond : SourceEdgeFragment current croApp.site.net (.inl ()) edge position)
    (targetFirst targetSecond : SourceEdgeFragment current croApp.site.reduce (.inl ()) edge position) :
    targetFirst.segments=targetSecond.segments ↔sourceFirst.segments=sourceSecond.segments := by
  obtain ⟨flow,_,_,_,_⟩ := cro_certified
  obtain ⟨principal⟩ := croApp.site.actionPrincipal_exists
  obtain ⟨sourceParent,word,_⟩ := Matches.observation croApp.site.net FunctionWrappedConsumer.source_matches
    (⟨[.fn],rfl⟩ : Position current.erase)
  have sourceWord : position=accessWord croApp.site.net sourceParent.val++[.body] := by rw [word];rfl
  have targetWord : position=accessWord croApp.site.reduce WrappedLambdaParent.finalParent.val++[.body] := by
    change _=accessWord croApp.site.reduce WrappedLambdaParent.finalEdges++[.body]
    rw [WrappedLambdaParent.finalWord];rfl
  exact sourceFirst.cro_kept_parent_copied_app_context_equality croApp.site
    (croApp.sourceIso.flowBalance flow) (.inl ()) rfl FunctionWrappedConsumer.source_matches actual_final_matches
    principal targetFirst sourceSecond targetSecond role role sourceParent sourceParent
    WrappedLambdaParent.finalParent WrappedLambdaParent.finalParent sourceWord sourceWord targetWord targetWord
    ⟨FunctionWrappedBodyParent.copiedLambda4,.inl ()⟩ ⟨FunctionWrappedBodyParent.copiedLambda4,.inl ()⟩ WrappedLambdaParent.finalFinish WrappedLambdaParent.finalFinish
    (actual_copied_app_finish targetFirst) (actual_copied_app_finish targetSecond)

theorem actual_fragments :
    Nonempty (SourceEdgeFragment current croApp.site.net (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current croApp.site.reduce (.inl ()) edge position) :=
  ⟨FunctionWrappedConsumer.source_matches.base_source_edge_fragment WrappedSuccessfulChains.targetClosed occurrence,
    actual_final_matches.base_source_edge_fragment WrappedSuccessfulChains.targetClosed occurrence⟩

/-- BODY is genuinely auxiliary and never a prerequisite reading edge.
Its lambda/APP endpoints separately have successful chains, making this
same-INIT reader-normalization regression nonvacuous for the Aux frontier. -/
theorem actual_reachable_auxiliary_app_context_comparison :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet croApp.site.reduce)
      [.beta 0,.croAction .lam 0 1 (by decide),.croAction .cro 0 1 (by decide),.croAction .app 0 1 (by decide)] ∧
    Matches croApp.site.net (.inl ()) current.erase ∧Matches croApp.site.reduce (.inl ()) current.erase ∧
    AuxiliaryAt current position ∧
    EndpointChain current (SyntaxIncidence.source current bodyEdge) [[.fn]] ∧
    EndpointChain current (SyntaxIncidence.target current WrappedSuccessfulChains.targetClosed bodyEdge) WrappedSuccessfulChains.bodyEdges ∧
    Nonempty (SourceEdgeFragment current croApp.site.net (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current croApp.site.reduce (.inl ()) edge position) ∧
    ∀ (sourceFirst sourceSecond : SourceEdgeFragment current croApp.site.net (.inl ()) edge position)
      (targetFirst targetSecond : SourceEdgeFragment current croApp.site.reduce (.inl ()) edge position),
      targetFirst.segments=targetSecond.segments ↔sourceFirst.segments=sourceSecond.segments := by
  obtain ⟨sourceExists,targetExists⟩ := actual_fragments
  obtain ⟨sourceChain,targetChain⟩ := UnaryLambdaBodyConsumer.Cro.endpoint_chains
  exact ⟨WrappedSuccessfulChains.initial,WrappedSuccessfulChains.sourceClosed,WrappedSuccessfulChains.actualHistory,actual_four_step_trace,
    FunctionWrappedConsumer.source_matches,actual_final_matches,auxiliary,sourceChain,targetChain,
    sourceExists,targetExists,actual_body_reader_pair⟩
#print axioms auxiliary
#print axioms never_reading_member
#print axioms actual_copied_app_finish
#print axioms actual_body_reader_pair
#print axioms actual_reachable_auxiliary_app_context_comparison
end Cro
namespace Bra
open AG Graph Lambda Lambda.Labelled BraFunctionReachable
abbrev position : Path := UnaryLambdaBodyConsumer.Bra.position
abbrev edge := UnaryLambdaBodyConsumer.Bra.edge
abbrev bodyEdge : SyntaxIncidence.Edge current := UnaryLambdaBodyConsumer.Bra.bodyEdge

def occurrence := UnaryLambdaBodyConsumer.Bra.occurrence
theorem role : SourceDeparture UnaryLambdaBodyConsumer.Bra.lambdaTerm .body edge.fromPort :=
  UnaryLambdaBodyConsumer.Bra.role

theorem auxiliary : AuxiliaryAt current position := UnaryLambdaBodyConsumer.Bra.auxiliary
theorem never_reading_member (chain : PrerequisiteChain current p es) : position∉es :=
  UnaryLambdaBodyConsumer.Bra.never_reading_member chain

theorem actual_copied_app_finish
    (fragment : SourceEdgeFragment current braApp.site.reduce (.inl ()) edge position) :
    fragment.access.val.getLast?=some (braApp.site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)) := by
  have same : BraFunctionConsumer.appParent=fragment.access :=
    actual_final_matches.accessWord_injective (BraFunctionConsumer.appParentWord.trans fragment.word.symm)
  rw [←same]
  exact BraFunctionConsumer.appParentFinish

theorem actual_body_reader_pair
    (sourceFirst sourceSecond : SourceEdgeFragment current braApp.site.net (.inl ()) edge position)
    (targetFirst targetSecond : SourceEdgeFragment current braApp.site.reduce (.inl ()) edge position) :
    targetFirst.segments=targetSecond.segments ↔sourceFirst.segments=sourceSecond.segments := by
  obtain ⟨flow,_,_,_,_⟩ := cro_certified
  obtain ⟨principal⟩ := braApp.site.actionPrincipal_exists
  obtain ⟨sourceParent,word,_⟩ := Matches.observation braApp.site.net BraFunctionConsumer.source_matches
    (⟨[.arg],rfl⟩ : Position current.erase)
  have sourceWord : position=accessWord braApp.site.net sourceParent.val++[.body] := by rw [word];rfl
  have targetWord : position=accessWord braApp.site.reduce BraArgumentParent.finalParent.val++[.body] := by
    change _=accessWord braApp.site.reduce BraArgumentParent.finalEdges++[.body]
    rw [BraArgumentParent.finalWord];rfl
  exact sourceFirst.bra_kept_parent_copied_app_context_equality braApp.site
    (braApp.sourceIso.flowBalance flow) (.inl ()) rfl BraFunctionConsumer.source_matches actual_final_matches
    principal targetFirst sourceSecond targetSecond role role sourceParent sourceParent
    BraArgumentParent.finalParent BraArgumentParent.finalParent sourceWord sourceWord targetWord targetWord
    ⟨BraFunctionBodyParent.copiedLambda4,.inl ()⟩ ⟨BraFunctionBodyParent.copiedLambda4,.inl ()⟩ BraArgumentParent.finalFinish BraArgumentParent.finalFinish
    (actual_copied_app_finish targetFirst) (actual_copied_app_finish targetSecond)

theorem actual_fragments :
    Nonempty (SourceEdgeFragment current braApp.site.net (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current braApp.site.reduce (.inl ()) edge position) :=
  ⟨BraFunctionConsumer.source_matches.base_source_edge_fragment BraSuccessfulChains.targetClosed occurrence,
    actual_final_matches.base_source_edge_fragment BraSuccessfulChains.targetClosed occurrence⟩

/-- BODY is genuinely auxiliary and never a prerequisite reading edge.
Its lambda/APP endpoints separately have successful chains, making this
same-INIT reader-normalization regression nonvacuous for the Aux frontier. -/
theorem actual_reachable_auxiliary_app_context_comparison :
    INIT original ∧Closed original.erase ∧History [[]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet braApp.site.reduce)
      [.beta 0,.braAction .lam 0 1 (by decide),.braAction .cro 0 1 (by decide),.braAction .app 0 1 (by decide)] ∧
    Matches braApp.site.net (.inl ()) current.erase ∧Matches braApp.site.reduce (.inl ()) current.erase ∧
    AuxiliaryAt current position ∧
    EndpointChain current (SyntaxIncidence.source current bodyEdge) [[.arg],[.fn]] ∧
    EndpointChain current (SyntaxIncidence.target current BraSuccessfulChains.targetClosed bodyEdge) BraSuccessfulChains.bodyEdges ∧
    Nonempty (SourceEdgeFragment current braApp.site.net (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current braApp.site.reduce (.inl ()) edge position) ∧
    ∀ (sourceFirst sourceSecond : SourceEdgeFragment current braApp.site.net (.inl ()) edge position)
      (targetFirst targetSecond : SourceEdgeFragment current braApp.site.reduce (.inl ()) edge position),
      targetFirst.segments=targetSecond.segments ↔sourceFirst.segments=sourceSecond.segments := by
  obtain ⟨sourceExists,targetExists⟩ := actual_fragments
  obtain ⟨sourceChain,targetChain⟩ := UnaryLambdaBodyConsumer.Bra.endpoint_chains
  exact ⟨BraSuccessfulChains.initial,BraSuccessfulChains.sourceClosed,BraSuccessfulChains.actualHistory,actual_four_step_trace,
    BraFunctionConsumer.source_matches,actual_final_matches,auxiliary,sourceChain,targetChain,
    sourceExists,targetExists,actual_body_reader_pair⟩
#print axioms auxiliary
#print axioms never_reading_member
#print axioms actual_copied_app_finish
#print axioms actual_body_reader_pair
#print axioms actual_reachable_auxiliary_app_context_comparison
end Bra
end Lamping.Checks.UnaryAppContextConsumer
