import Lamping.Lamping.FanBodyFragmentReflection
import Lamping.Checks.FanBodyFragmentTransportConsumer
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanBodyFragmentReflectionConsumer
open AG Graph Lambda Lambda.Labelled FanBodyDoubleLambdaReachable FanBodyDoubleLambdaParents
open FanBodyFragmentTransportConsumer

theorem outer_target_incoming (selection : OccurrenceFragmentSelection current outerTarget (.inl ())) :
    ∃stamp,(selection bodyPosition).context=.lamBody stamp := by
  have same := (selection bodyPosition).occurrence.same_occurrence FanBodyContextConsumer.leftOccurrence
  exact ⟨_,same.2.1⟩
theorem inner_target_incoming (selection : OccurrenceFragmentSelection current innerTarget (.inl ())) :
    ∃stamp,(selection bodyPosition).context=.lamBody stamp := by
  have same := (selection bodyPosition).occurrence.same_occurrence FanBodyContextConsumer.leftOccurrence
  exact ⟨_,same.2.1⟩
/-- Target samechain representation is supplied by reflexivity, and arbitrary
OLD occurrence choices are reflected through the actual outer action. -/
theorem actual_outer_reflect (principal : SiteActionPrincipal outerFan.site)
    (selection : OccurrenceFragmentSelection current outerTarget (.inl ()))
    (sourceFirst sourceSecond : OccurrenceFragment current outerSource (.inl ()) bodyPosition.val) :
    sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  have chosen : (selection bodyPosition).fragment.access=bodyChild := FanBodyOuterCutConsumer.target_matches.accessWord_injective
    ((selection bodyPosition).fragment.word.trans bodyWord.symm)
  have finish : (selection bodyPosition).fragment.access.val.getLast?=some
      (outerTarget.wire (.inl ⟨.inl innerKept2,.inl ()⟩)) := by rw [chosen];exact bodyFinish
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  exact outerFan.site.fan_body_copied_parent_same_slot_reflect
    FanBodyOuterCutConsumer.source_matches FanBodyOuterCutConsumer.target_matches
    (outerFan.sourceIso.flowBalance flow) rfl principal selection
    FanBodyContextConsumer.leftChain FanBodyContextConsumer.leftChain rfl bodyPosition bodyPosition (n:=0) rfl rfl
    (outer_target_incoming selection) (outer_target_incoming selection) sourceFirst sourceSecond lambdaParent lambdaParent
    (by change bodyPosition.val=accessWord outerNet lambdaEdges++[.body];rw [lambdaWord];rfl)
    (by change bodyPosition.val=accessWord outerNet lambdaEdges++[.body];rw [lambdaWord];rfl)
    false false lambdaFinish lambdaFinish ⟨innerKept2,.inl ()⟩ ⟨innerKept2,.inl ()⟩ finish finish

/-- The actual inner copied-context finite endpoint is obtained from Matches,
while the high-level theorem supplies target equality from its whole image. -/
theorem actual_inner_reflect (principal : SiteActionPrincipal innerFan.site)
    (selection : OccurrenceFragmentSelection current innerTarget (.inl ()))
    (sourceFirst sourceSecond : OccurrenceFragment current innerSource (.inl ()) bodyPosition.val) :
    sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  obtain ⟨parent,parentPort,parentWord,parentFinish⟩ := final_parent_kept principal
  obtain ⟨child,branch,childWord,childFinish⟩ := final_child_copied principal
  have chosen : (selection bodyPosition).fragment.access=child := actual_final_matches.accessWord_injective
    ((selection bodyPosition).fragment.word.trans childWord.symm)
  have finish : (selection bodyPosition).fragment.access.val.getLast?=some
      (innerTarget.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)) := by rw [chosen];exact childFinish
  obtain ⟨flow,_,_,_,_⟩ := outer_certified
  exact innerFan.site.fan_body_kept_parent_same_slot_reflect actual_inner_source_matches actual_final_matches
    (innerFan.sourceIso.flowBalance flow) rfl principal selection
    FanBodyContextConsumer.leftChain FanBodyContextConsumer.leftChain rfl bodyPosition bodyPosition (n:=0) rfl rfl
    (inner_target_incoming selection) (inner_target_incoming selection) sourceFirst sourceSecond parent parent
    (by rw [parentWord];rfl) (by rw [parentWord];rfl)
    parentPort parentPort parentFinish parentFinish branch branch finish finish

theorem actual_outer_supply :
    INIT original ∧History [[]] original current ∧Closed original.erase ∧Closed current.erase ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet outerTarget) [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    Matches outerSource (.inl ()) current.erase ∧Matches outerTarget (.inl ()) current.erase ∧
    Nonempty (OccurrenceFragmentSelection current outerSource (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current outerTarget (.inl ())) ∧
    PrerequisiteChain current bodyPosition.val [bodyPosition.val,[.fn]] ∧
    ∃_principal : SiteActionPrincipal outerFan.site,
      ∀ (sourceFirst sourceSecond : OccurrenceFragmentSelection current outerSource (.inl ()))
        (targetFirst targetSecond : OccurrenceFragmentSelection current outerTarget (.inl ())),
        (sourceFirst bodyPosition).fragment.segments=(sourceSecond bodyPosition).fragment.segments ∧
        (targetFirst bodyPosition).fragment.segments=(targetSecond bodyPosition).fragment.segments := by
  refine ⟨FanBodyContextConsumer.initial,FanBodyContextConsumer.actualHistory,FanBodyContextConsumer.closed,
    FanBodyContextConsumer.targetClosed,.cons concrete.graph_step (.cons outerFan.graph_step (.refl _)),
    FanBodyOuterCutConsumer.source_matches,FanBodyOuterCutConsumer.target_matches,
    FanBodyOuterCutConsumer.source_matches.occurrence_fragment_selection FanBodyContextConsumer.targetClosed,
    FanBodyOuterCutConsumer.target_matches.occurrence_fragment_selection FanBodyContextConsumer.targetClosed,
    FanBodyContextConsumer.leftChain,?_⟩
  obtain ⟨principal⟩ := outerFan.site.actionPrincipal_exists
  exact ⟨principal,fun sourceFirst sourceSecond targetFirst targetSecond =>
    ⟨actual_outer_reflect principal targetFirst (sourceFirst bodyPosition) (sourceSecond bodyPosition),
      OccurrenceFragment.segments_unique FanBodyOuterCutConsumer.target_matches _ _⟩⟩

theorem actual_inner_supply :
    INIT original ∧History [[]] original current ∧Closed original.erase ∧Closed current.erase ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet innerTarget)
      [.beta 0,.fanAction .lam 0 1 (by decide),.fanAction .lam 0 1 (by decide)] ∧
    Matches innerSource (.inl ()) current.erase ∧Matches innerTarget (.inl ()) current.erase ∧
    Nonempty (OccurrenceFragmentSelection current innerSource (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current innerTarget (.inl ())) ∧
    PrerequisiteChain current bodyPosition.val [bodyPosition.val,[.fn]] ∧
    ∃_principal : SiteActionPrincipal innerFan.site,
      ∀ (sourceFirst sourceSecond : OccurrenceFragmentSelection current innerSource (.inl ()))
        (targetFirst targetSecond : OccurrenceFragmentSelection current innerTarget (.inl ())),
        (sourceFirst bodyPosition).fragment.segments=(sourceSecond bodyPosition).fragment.segments ∧
        (targetFirst bodyPosition).fragment.segments=(targetSecond bodyPosition).fragment.segments := by
  refine ⟨FanBodyContextConsumer.initial,FanBodyContextConsumer.actualHistory,FanBodyContextConsumer.closed,
    FanBodyContextConsumer.targetClosed,actual_three_step_trace,actual_inner_source_matches,actual_final_matches,
    actual_inner_source_matches.occurrence_fragment_selection FanBodyContextConsumer.targetClosed,
    actual_final_matches.occurrence_fragment_selection FanBodyContextConsumer.targetClosed,
    FanBodyContextConsumer.leftChain,?_⟩
  obtain ⟨principal⟩ := innerFan.site.actionPrincipal_exists
  exact ⟨principal,fun sourceFirst sourceSecond targetFirst targetSecond =>
    ⟨actual_inner_reflect principal targetFirst (sourceFirst bodyPosition) (sourceSecond bodyPosition),
      OccurrenceFragment.segments_unique actual_final_matches _ _⟩⟩
end Lamping.Checks.FanBodyFragmentReflectionConsumer
#print axioms Lamping.Checks.FanBodyFragmentReflectionConsumer.actual_outer_reflect
#print axioms Lamping.Checks.FanBodyFragmentReflectionConsumer.actual_inner_reflect
#print axioms Lamping.Checks.FanBodyFragmentReflectionConsumer.actual_outer_supply
#print axioms Lamping.Checks.FanBodyFragmentReflectionConsumer.actual_inner_supply
