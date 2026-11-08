import Lamping.Lamping.FanBodyFragmentTransport
import Lamping.Checks.FanBodyOuterCutConsumer
import Lamping.Checks.FanBodySequentialCutsConsumer
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanBodyFragmentTransportConsumer
open AG Graph Lambda Lambda.Labelled FanBodyDoubleLambdaReachable FanBodyDoubleLambdaParents
abbrev bodyPosition : Position current.erase := ⟨[.fn,.body],rfl⟩
noncomputable abbrev outerSource := outerFan.site.net
noncomputable abbrev outerTarget := outerFan.site.reduce
noncomputable abbrev innerSource := innerFan.site.net
noncomputable abbrev innerTarget := innerFan.site.reduce

theorem outer_incoming (selection : OccurrenceFragmentSelection current outerSource (.inl ())) :
    ∃stamp,(selection bodyPosition).context=.lamBody stamp := by
  have same := (selection bodyPosition).occurrence.same_occurrence FanBodyContextConsumer.leftOccurrence
  exact ⟨_,same.2.1⟩
theorem inner_incoming (selection : OccurrenceFragmentSelection current innerSource (.inl ())) :
    ∃stamp,(selection bodyPosition).context=.lamBody stamp := by
  have same := (selection bodyPosition).occurrence.same_occurrence FanBodyContextConsumer.leftOccurrence
  exact ⟨_,same.2.1⟩

/-- Full actual outer BODY pieces transport at successful slot0. The source
representation input is the real samechain reflexivity; parent slot1/Bool are
still derived by the general theorem, not supplied as a profile. -/
theorem actual_outer_forward (principal : SiteActionPrincipal outerFan.site)
    (selection : OccurrenceFragmentSelection current outerSource (.inl ()))
    (targetFirst targetSecond : OccurrenceFragment current outerTarget (.inl ()) bodyPosition.val) :
    targetFirst.fragment.segments=targetSecond.fragment.segments := by
  have firstAccess : targetFirst.fragment.access=bodyChild := FanBodyOuterCutConsumer.target_matches.accessWord_injective
    (targetFirst.fragment.word.trans bodyWord.symm)
  have secondAccess : targetSecond.fragment.access=bodyChild := FanBodyOuterCutConsumer.target_matches.accessWord_injective
    (targetSecond.fragment.word.trans bodyWord.symm)
  have firstEnd : targetFirst.fragment.access.val.getLast?=some
      (outerTarget.wire (.inl ⟨.inl innerKept2,.inl ()⟩)) := by rw [firstAccess];exact bodyFinish
  have secondEnd : targetSecond.fragment.access.val.getLast?=some
      (outerTarget.wire (.inl ⟨.inl innerKept2,.inl ()⟩)) := by rw [secondAccess];exact bodyFinish
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  exact outerFan.site.fan_body_copied_parent_same_slot_forward
    FanBodyOuterCutConsumer.source_matches FanBodyOuterCutConsumer.target_matches
    (outerFan.sourceIso.flowBalance flow) rfl principal selection
    FanBodyContextConsumer.leftChain FanBodyContextConsumer.leftChain rfl bodyPosition bodyPosition (n:=0) rfl rfl
    (show current.subterm bodyPosition.val=some (.lam FanBodyContextConsumer.functionBody.label
      FanBodyContextConsumer.innerBody) from rfl)
    (show current.subterm bodyPosition.val=some (.lam FanBodyContextConsumer.functionBody.label
      FanBodyContextConsumer.innerBody) from rfl)
    (outer_incoming selection) (outer_incoming selection) targetFirst targetSecond lambdaParent lambdaParent
    (by change bodyPosition.val=accessWord outerNet lambdaEdges++[.body];rw [lambdaWord];rfl)
    (by change bodyPosition.val=accessWord outerNet lambdaEdges++[.body];rw [lambdaWord];rfl)
    false false lambdaFinish lambdaFinish ⟨innerKept2,.inl ()⟩ ⟨innerKept2,.inl ()⟩ firstEnd secondEnd

/-- Full actual inner BODY pieces transport at successful slot0. Actual
endpoint supply is from the same three-rule fixture and actual Matches. -/
theorem actual_inner_forward (principal : SiteActionPrincipal innerFan.site)
    (selection : OccurrenceFragmentSelection current innerSource (.inl ()))
    (targetFirst targetSecond : OccurrenceFragment current innerTarget (.inl ()) bodyPosition.val) :
    targetFirst.fragment.segments=targetSecond.fragment.segments := by
  obtain ⟨parent,parentPort,parentWord,parentFinish⟩ := final_parent_kept principal
  obtain ⟨child,branch,childWord,childFinish⟩ := final_child_copied principal
  have firstAccess : targetFirst.fragment.access=child := actual_final_matches.accessWord_injective
    (targetFirst.fragment.word.trans childWord.symm)
  have secondAccess : targetSecond.fragment.access=child := actual_final_matches.accessWord_injective
    (targetSecond.fragment.word.trans childWord.symm)
  have firstEnd : targetFirst.fragment.access.val.getLast?=some
      (innerTarget.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)) := by rw [firstAccess];exact childFinish
  have secondEnd : targetSecond.fragment.access.val.getLast?=some
      (innerTarget.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)) := by rw [secondAccess];exact childFinish
  obtain ⟨flow,_,_,_,_⟩ := outer_certified
  exact innerFan.site.fan_body_kept_parent_same_slot_forward actual_inner_source_matches actual_final_matches
    (innerFan.sourceIso.flowBalance flow) rfl principal selection
    FanBodyContextConsumer.leftChain FanBodyContextConsumer.leftChain rfl bodyPosition bodyPosition (n:=0) rfl rfl
    (inner_incoming selection) (inner_incoming selection) targetFirst targetSecond parent parent
    (by rw [parentWord];rfl) (by rw [parentWord];rfl)
    parentPort parentPort parentFinish parentFinish branch branch firstEnd secondEnd

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
    ⟨OccurrenceFragment.segments_unique FanBodyOuterCutConsumer.source_matches _ _,
      actual_outer_forward principal sourceFirst (targetFirst bodyPosition) (targetSecond bodyPosition)⟩⟩

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
    ⟨OccurrenceFragment.segments_unique actual_inner_source_matches _ _,
      actual_inner_forward principal sourceFirst (targetFirst bodyPosition) (targetSecond bodyPosition)⟩⟩
end Lamping.Checks.FanBodyFragmentTransportConsumer
#print axioms Lamping.Checks.FanBodyFragmentTransportConsumer.actual_outer_forward
#print axioms Lamping.Checks.FanBodyFragmentTransportConsumer.actual_inner_forward
#print axioms Lamping.Checks.FanBodyFragmentTransportConsumer.actual_outer_supply
#print axioms Lamping.Checks.FanBodyFragmentTransportConsumer.actual_inner_supply
