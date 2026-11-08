import Lamping.Lamping.FanLambdaMixedSeparation
import Lamping.Checks.FanBodyFragmentTransportConsumer
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanBodyMixedConsumer
open AG Graph Lambda Lambda.Labelled FanBodyDoubleLambdaReachable FanBodyDoubleLambdaParents
abbrev bodyPosition : Position current.erase := ⟨[.fn,.body],rfl⟩
abbrev fnPosition : Position current.erase := ⟨[.fn],rfl⟩
abbrev bodyEdge := FanBodyOuterCutConsumer.bodyEdge
abbrev fnEdge := sourceEdge [] (.appFn current.label) FanBodyContextConsumer.functionTerm
def fnOccurrence : SourceSubterm [] .external current fnPosition.val [] (.appFn current.label)
    FanBodyContextConsumer.functionTerm := .fn .nil
def fnRole : SourceDeparture current .fn fnEdge.fromPort := .fn
def fnChain : PrerequisiteChain current fnPosition.val [[.fn]] := .redex_lam (p:=[]) rfl
noncomputable abbrev sourceNet := outerFan.site.net
noncomputable abbrev targetNet := outerFan.site.reduce

theorem actual_parent_mixed (principal : SiteActionPrincipal outerFan.site)
    (sourceBody : SourceEdgeFragment current sourceNet (.inl ()) bodyEdge bodyPosition.val)
    (targetBody : SourceEdgeFragment current targetNet (.inl ()) bodyEdge bodyPosition.val)
    (sourceFn : SourceEdgeFragment current sourceNet (.inl ()) fnEdge fnPosition.val)
    (targetFn : SourceEdgeFragment current targetNet (.inl ()) fnEdge fnPosition.val) :
    sourceBody.segments≠sourceFn.segments ∧targetBody.segments≠targetFn.segments := by
  obtain ⟨sourceParent,parentWord,_⟩ := Matches.observation _ FanBodyOuterCutConsumer.source_matches fnPosition
  obtain ⟨sourceRoot,rootWord,_⟩ := Matches.observation _ FanBodyOuterCutConsumer.source_matches
    (show Position current.erase from ⟨[],rfl⟩)
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  exact sourceBody.fan_lambda_copied_parent_vs_kept_parent outerFan.site
    (outerFan.sourceIso.flowBalance flow) (.inl ()) rfl
    FanBodyOuterCutConsumer.source_matches FanBodyOuterCutConsumer.target_matches principal
    targetBody sourceFn targetFn FanBodyOuterCutConsumer.role fnRole
    sourceParent sourceRoot lambdaParent rootAccess
    (by rw [parentWord];rfl) (by rw [rootWord];rfl)
    (by change bodyPosition.val=accessWord outerNet lambdaEdges++[.body];rw [lambdaWord];rfl)
    (by rfl) false lambdaFinish finalApp appCtx rootFinish

theorem actual_terminal_mixed (principal : SiteActionPrincipal outerFan.site)
    (sourceBody : SourceEdgeFragment current sourceNet (.inl ()) bodyEdge bodyPosition.val)
    (targetBody : SourceEdgeFragment current targetNet (.inl ()) bodyEdge bodyPosition.val)
    (sourceFn : SourceEdgeFragment current sourceNet (.inl ()) fnEdge fnPosition.val)
    (targetFn : SourceEdgeFragment current targetNet (.inl ()) fnEdge fnPosition.val) :
    sourceFn.segments≠sourceBody.segments ∧targetFn.segments≠targetBody.segments := by
  have fnAccess : targetFn.access=lambdaParent := FanBodyOuterCutConsumer.target_matches.accessWord_injective
    (targetFn.word.trans lambdaWord.symm)
  have bodyAccess : targetBody.access=bodyChild := FanBodyOuterCutConsumer.target_matches.accessWord_injective
    (targetBody.word.trans bodyWord.symm)
  have fnFinish : targetFn.access.val.getLast?=some (targetNet.wire (.inl ⟨.inr (.inl false),.inl ()⟩)) := by
    rw [fnAccess];exact lambdaFinish
  have bodyAt : targetBody.access.val.getLast?=some (targetNet.wire (.inl ⟨.inl innerKept2,.inl ()⟩)) := by
    rw [bodyAccess];exact bodyFinish
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  exact sourceFn.fan_lambda_copied_context_vs_kept_terminal outerFan.site
    (outerFan.sourceIso.flowBalance flow) (.inl ()) rfl FanBodyOuterCutConsumer.source_matches principal
    targetFn sourceBody targetBody false fnFinish innerKept2 (.inl ()) bodyAt

theorem actual_common_slot_exclusion (principal : SiteActionPrincipal outerFan.site)
    (sourceBody : SourceEdgeFragment current sourceNet (.inl ()) bodyEdge bodyPosition.val)
    (targetBody : SourceEdgeFragment current targetNet (.inl ()) bodyEdge bodyPosition.val)
    (sourceFn : SourceEdgeFragment current sourceNet (.inl ()) fnEdge fnPosition.val)
    (targetFn : SourceEdgeFragment current targetNet (.inl ()) fnEdge fnPosition.val)
    (sourceSelection : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (targetSelection : OccurrenceFragmentSelection current targetNet (.inl ())) :
    ¬SameChainRepresentation sourceSelection FanBodyContextConsumer.leftChain fnChain ∧
      ¬SameChainRepresentation targetSelection FanBodyContextConsumer.leftChain fnChain := by
  obtain ⟨sourceParent,parentWord,_⟩ := Matches.observation _ FanBodyOuterCutConsumer.source_matches fnPosition
  obtain ⟨sourceRoot,rootWord,_⟩ := Matches.observation _ FanBodyOuterCutConsumer.source_matches
    (show Position current.erase from ⟨[],rfl⟩)
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  exact outerFan.site.fan_lambda_mixed_parent_slot_exclusion (outerFan.sourceIso.flowBalance flow) (.inl ()) rfl
    FanBodyOuterCutConsumer.source_matches FanBodyOuterCutConsumer.target_matches principal bodyPosition fnPosition
    ⟨_,_,_,FanBodyContextConsumer.leftOccurrence,sourceBody⟩
    ⟨_,_,_,FanBodyContextConsumer.leftOccurrence,targetBody⟩
    ⟨_,_,_,fnOccurrence,sourceFn⟩ ⟨_,_,_,fnOccurrence,targetFn⟩
    FanBodyOuterCutConsumer.role fnRole
    sourceParent sourceRoot lambdaParent rootAccess
    (by rw [parentWord];rfl) (by rw [rootWord];rfl)
    (by change bodyPosition.val=accessWord outerNet lambdaEdges++[.body];rw [lambdaWord];rfl)
    (by rfl) false lambdaFinish finalApp appCtx rootFinish sourceSelection targetSelection
    FanBodyContextConsumer.leftChain fnChain (n:=0) rfl rfl

/-- The terminal guard consumes its own slot equality in the opposite order;
its real copied/kept finishes are supplied by these SAME actual accesses. -/
theorem actual_terminal_slot_exclusion (principal : SiteActionPrincipal outerFan.site)
    (sourceBody : SourceEdgeFragment current sourceNet (.inl ()) bodyEdge bodyPosition.val)
    (targetBody : SourceEdgeFragment current targetNet (.inl ()) bodyEdge bodyPosition.val)
    (sourceFn : SourceEdgeFragment current sourceNet (.inl ()) fnEdge fnPosition.val)
    (targetFn : SourceEdgeFragment current targetNet (.inl ()) fnEdge fnPosition.val)
    (sourceSelection : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (targetSelection : OccurrenceFragmentSelection current targetNet (.inl ())) :
    ¬SameChainRepresentation sourceSelection fnChain FanBodyContextConsumer.leftChain ∧
      ¬SameChainRepresentation targetSelection fnChain FanBodyContextConsumer.leftChain := by
  have fnAccess : targetFn.access=lambdaParent := FanBodyOuterCutConsumer.target_matches.accessWord_injective
    (targetFn.word.trans lambdaWord.symm)
  have bodyAccess : targetBody.access=bodyChild := FanBodyOuterCutConsumer.target_matches.accessWord_injective
    (targetBody.word.trans bodyWord.symm)
  have fnFinish : targetFn.access.val.getLast?=some (targetNet.wire (.inl ⟨.inr (.inl false),.inl ()⟩)) := by
    rw [fnAccess];exact lambdaFinish
  have bodyAt : targetBody.access.val.getLast?=some (targetNet.wire (.inl ⟨.inl innerKept2,.inl ()⟩)) := by
    rw [bodyAccess];exact bodyFinish
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  exact outerFan.site.fan_lambda_mixed_terminal_slot_exclusion (outerFan.sourceIso.flowBalance flow) (.inl ()) rfl
    FanBodyOuterCutConsumer.source_matches FanBodyOuterCutConsumer.target_matches principal fnPosition bodyPosition
    ⟨_,_,_,fnOccurrence,sourceFn⟩ ⟨_,_,_,fnOccurrence,targetFn⟩
    ⟨_,_,_,FanBodyContextConsumer.leftOccurrence,sourceBody⟩
    ⟨_,_,_,FanBodyContextConsumer.leftOccurrence,targetBody⟩
    false fnFinish innerKept2 (.inl ()) bodyAt sourceSelection targetSelection
    fnChain FanBodyContextConsumer.leftChain (n:=0) rfl rfl

/-- Different actual BODY/rootFN occurrences, with true successful chains of
length two/one. Neither source nor target representation truth is assumed. -/
theorem actual_mixed_supply :
    INIT original ∧History [[]] original current ∧Closed original.erase ∧Closed current.erase ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet targetNet)
      [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    Matches sourceNet (.inl ()) current.erase ∧Matches targetNet (.inl ()) current.erase ∧
    bodyPosition.val≠fnPosition.val ∧
    PrerequisiteChain current bodyPosition.val [bodyPosition.val,[.fn]] ∧
    PrerequisiteChain current fnPosition.val [[.fn]] ∧
    Nonempty (SourceEdgeFragment current sourceNet (.inl ()) bodyEdge bodyPosition.val) ∧
    Nonempty (SourceEdgeFragment current targetNet (.inl ()) bodyEdge bodyPosition.val) ∧
    Nonempty (SourceEdgeFragment current sourceNet (.inl ()) fnEdge fnPosition.val) ∧
    Nonempty (SourceEdgeFragment current targetNet (.inl ()) fnEdge fnPosition.val) ∧
    Nonempty (OccurrenceFragmentSelection current sourceNet (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current targetNet (.inl ())) ∧
    ∃_principal : SiteActionPrincipal outerFan.site,
      ∀ (sourceBody : SourceEdgeFragment current sourceNet (.inl ()) bodyEdge bodyPosition.val)
        (targetBody : SourceEdgeFragment current targetNet (.inl ()) bodyEdge bodyPosition.val)
        (sourceFn : SourceEdgeFragment current sourceNet (.inl ()) fnEdge fnPosition.val)
        (targetFn : SourceEdgeFragment current targetNet (.inl ()) fnEdge fnPosition.val)
        (sourceSelection : OccurrenceFragmentSelection current sourceNet (.inl ()))
        (targetSelection : OccurrenceFragmentSelection current targetNet (.inl ())),
        (sourceBody.segments≠sourceFn.segments ∧targetBody.segments≠targetFn.segments) ∧
        (sourceFn.segments≠sourceBody.segments ∧targetFn.segments≠targetBody.segments) ∧
        (¬SameChainRepresentation sourceSelection FanBodyContextConsumer.leftChain fnChain ∧
          ¬SameChainRepresentation targetSelection FanBodyContextConsumer.leftChain fnChain) ∧
        (¬SameChainRepresentation sourceSelection fnChain FanBodyContextConsumer.leftChain ∧
          ¬SameChainRepresentation targetSelection fnChain FanBodyContextConsumer.leftChain) := by
  refine ⟨FanBodyContextConsumer.initial,FanBodyContextConsumer.actualHistory,FanBodyContextConsumer.closed,
    FanBodyContextConsumer.targetClosed,.cons concrete.graph_step (.cons outerFan.graph_step (.refl _)),
    FanBodyOuterCutConsumer.source_matches,FanBodyOuterCutConsumer.target_matches,(by decide),
    FanBodyContextConsumer.leftChain,fnChain,
    FanBodyOuterCutConsumer.source_matches.base_source_edge_fragment FanBodyContextConsumer.targetClosed FanBodyContextConsumer.leftOccurrence,
    FanBodyOuterCutConsumer.target_matches.base_source_edge_fragment FanBodyContextConsumer.targetClosed FanBodyContextConsumer.leftOccurrence,
    FanBodyOuterCutConsumer.source_matches.base_source_edge_fragment FanBodyContextConsumer.targetClosed fnOccurrence,
    FanBodyOuterCutConsumer.target_matches.base_source_edge_fragment FanBodyContextConsumer.targetClosed fnOccurrence,
    FanBodyOuterCutConsumer.source_matches.occurrence_fragment_selection FanBodyContextConsumer.targetClosed,
    FanBodyOuterCutConsumer.target_matches.occurrence_fragment_selection FanBodyContextConsumer.targetClosed,?_⟩
  obtain ⟨principal⟩ := outerFan.site.actionPrincipal_exists
  exact ⟨principal,fun sourceBody targetBody sourceFn targetFn sourceSelection targetSelection =>
    ⟨actual_parent_mixed principal sourceBody targetBody sourceFn targetFn,
      actual_terminal_mixed principal sourceBody targetBody sourceFn targetFn,
      actual_common_slot_exclusion principal sourceBody targetBody sourceFn targetFn sourceSelection targetSelection,
      actual_terminal_slot_exclusion principal sourceBody targetBody sourceFn targetFn sourceSelection targetSelection⟩⟩
end Lamping.Checks.FanBodyMixedConsumer
#print axioms Lamping.Checks.FanBodyMixedConsumer.actual_parent_mixed
#print axioms Lamping.Checks.FanBodyMixedConsumer.actual_terminal_mixed
#print axioms Lamping.Checks.FanBodyMixedConsumer.actual_common_slot_exclusion

#print axioms Lamping.Checks.FanBodyMixedConsumer.actual_terminal_slot_exclusion
#print axioms Lamping.Checks.FanBodyMixedConsumer.actual_mixed_supply
