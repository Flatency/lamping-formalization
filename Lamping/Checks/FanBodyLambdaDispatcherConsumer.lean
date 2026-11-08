import Lamping.Lamping.FanBodyLambdaDispatcher
import Lamping.Checks.FanBodyFragmentTransportConsumer
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanBodyLambdaDispatcherConsumer
open AG Graph Lambda Lambda.Labelled FanBodyDoubleLambdaReachable FanBodyDoubleLambdaParents
abbrev bodyPosition : Position current.erase := ⟨[.fn,.body],rfl⟩
/-- Literal BODY incoming is from the actual occurrence, for every legal selection. -/
theorem actual_incoming {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    (selection : OccurrenceFragmentSelection current g root) :
    ∃stamp,(selection bodyPosition).context=.lamBody stamp := by
  exact ⟨_,((selection bodyPosition).occurrence.same_occurrence FanBodyContextConsumer.leftOccurrence).2.1⟩

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
/-- Direct FULL dispatcher calls at the real K BODY slot, four arbitrary
choices. No parent/access/endpoints/Bool profile is provided by this caller. -/
theorem full_samechain_dispatch (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site)
    (sourceFirst sourceSecond : OccurrenceFragmentSelection current site.net root)
    (targetFirst targetSecond : OccurrenceFragmentSelection current site.reduce root) :
    (sourceFirst bodyPosition).fragment.segments=(sourceSecond bodyPosition).fragment.segments ∧
      (targetFirst bodyPosition).fragment.segments=(targetSecond bodyPosition).fragment.segments := by
  have lookup : current.subterm bodyPosition.val=some (.lam FanBodyContextConsumer.functionBody.label
      FanBodyContextConsumer.innerBody) := rfl
  have forward := site.fan_body_lambda_same_slot_forward sourceMatches targetMatches flow positive principal
    sourceFirst FanBodyContextConsumer.leftChain FanBodyContextConsumer.leftChain rfl
    bodyPosition bodyPosition (n:=0) rfl rfl lookup lookup
    (actual_incoming sourceFirst) (actual_incoming sourceFirst) (targetFirst bodyPosition) (targetSecond bodyPosition)
  have reflection := site.fan_body_lambda_same_slot_reflect sourceMatches targetMatches flow positive principal
    targetFirst FanBodyContextConsumer.leftChain FanBodyContextConsumer.leftChain rfl
    bodyPosition bodyPosition (n:=0) rfl rfl lookup lookup
    (actual_incoming targetFirst) (actual_incoming targetFirst) (sourceFirst bodyPosition) (sourceSecond bodyPosition)
  exact ⟨reflection,forward⟩
end

theorem actual_outer_pair (principal : SiteActionPrincipal outerFan.site)
    (sourceFirst sourceSecond : OccurrenceFragmentSelection current outerFan.site.net (.inl ()))
    (targetFirst targetSecond : OccurrenceFragmentSelection current outerFan.site.reduce (.inl ())) :
    (sourceFirst bodyPosition).fragment.segments=(sourceSecond bodyPosition).fragment.segments ∧
      (targetFirst bodyPosition).fragment.segments=(targetSecond bodyPosition).fragment.segments := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  exact full_samechain_dispatch outerFan.site FanBodyOuterCutConsumer.source_matches FanBodyOuterCutConsumer.target_matches
    (outerFan.sourceIso.flowBalance flow) rfl principal sourceFirst sourceSecond targetFirst targetSecond

theorem actual_inner_pair (principal : SiteActionPrincipal innerFan.site)
    (sourceFirst sourceSecond : OccurrenceFragmentSelection current innerFan.site.net (.inl ()))
    (targetFirst targetSecond : OccurrenceFragmentSelection current innerFan.site.reduce (.inl ())) :
    (sourceFirst bodyPosition).fragment.segments=(sourceSecond bodyPosition).fragment.segments ∧
      (targetFirst bodyPosition).fragment.segments=(targetSecond bodyPosition).fragment.segments := by
  obtain ⟨flow,_,_,_,_⟩ := outer_certified
  exact full_samechain_dispatch innerFan.site actual_inner_source_matches actual_final_matches
    (innerFan.sourceIso.flowBalance flow) rfl principal sourceFirst sourceSecond targetFirst targetSecond

/-- Real outer trace and fragment existence, not an asserted CC witness. -/
theorem actual_outer_supply :
    INIT original ∧History [[]] original current ∧Closed original.erase ∧Closed current.erase ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet outerFan.site.reduce)
      [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    Matches outerFan.site.net (.inl ()) current.erase ∧Matches outerFan.site.reduce (.inl ()) current.erase ∧
    Nonempty (OccurrenceFragmentSelection current outerFan.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current outerFan.site.reduce (.inl ())) ∧
    PrerequisiteChain current bodyPosition.val [bodyPosition.val,[.fn]] ∧
    ∃_principal : SiteActionPrincipal outerFan.site,
      ∀ (sourceFirst sourceSecond : OccurrenceFragmentSelection current outerFan.site.net (.inl ()))
        (targetFirst targetSecond : OccurrenceFragmentSelection current outerFan.site.reduce (.inl ())),
        (sourceFirst bodyPosition).fragment.segments=(sourceSecond bodyPosition).fragment.segments ∧
        (targetFirst bodyPosition).fragment.segments=(targetSecond bodyPosition).fragment.segments := by
  refine ⟨FanBodyContextConsumer.initial,FanBodyContextConsumer.actualHistory,FanBodyContextConsumer.closed,
    FanBodyContextConsumer.targetClosed,.cons concrete.graph_step (.cons outerFan.graph_step (.refl _)),
    FanBodyOuterCutConsumer.source_matches,FanBodyOuterCutConsumer.target_matches,
    FanBodyOuterCutConsumer.source_matches.occurrence_fragment_selection FanBodyContextConsumer.targetClosed,
    FanBodyOuterCutConsumer.target_matches.occurrence_fragment_selection FanBodyContextConsumer.targetClosed,
    FanBodyContextConsumer.leftChain,?_⟩
  obtain ⟨principal⟩ := outerFan.site.actionPrincipal_exists
  exact ⟨principal,actual_outer_pair principal⟩

/-- Real inner trace; serial natural cells are not SAME-site doublecopied. -/
theorem actual_inner_supply :
    INIT original ∧History [[]] original current ∧Closed original.erase ∧Closed current.erase ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet innerFan.site.reduce)
      [.beta 0,.fanAction .lam 0 1 (by decide),.fanAction .lam 0 1 (by decide)] ∧
    Matches innerFan.site.net (.inl ()) current.erase ∧Matches innerFan.site.reduce (.inl ()) current.erase ∧
    Nonempty (OccurrenceFragmentSelection current innerFan.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current innerFan.site.reduce (.inl ())) ∧
    PrerequisiteChain current bodyPosition.val [bodyPosition.val,[.fn]] ∧
    ∃_principal : SiteActionPrincipal innerFan.site,
      ∀ (sourceFirst sourceSecond : OccurrenceFragmentSelection current innerFan.site.net (.inl ()))
        (targetFirst targetSecond : OccurrenceFragmentSelection current innerFan.site.reduce (.inl ())),
        (sourceFirst bodyPosition).fragment.segments=(sourceSecond bodyPosition).fragment.segments ∧
        (targetFirst bodyPosition).fragment.segments=(targetSecond bodyPosition).fragment.segments := by
  refine ⟨FanBodyContextConsumer.initial,FanBodyContextConsumer.actualHistory,FanBodyContextConsumer.closed,
    FanBodyContextConsumer.targetClosed,actual_three_step_trace,actual_inner_source_matches,actual_final_matches,
    actual_inner_source_matches.occurrence_fragment_selection FanBodyContextConsumer.targetClosed,
    actual_final_matches.occurrence_fragment_selection FanBodyContextConsumer.targetClosed,
    FanBodyContextConsumer.leftChain,?_⟩
  obtain ⟨principal⟩ := innerFan.site.actionPrincipal_exists
  exact ⟨principal,actual_inner_pair principal⟩
end Lamping.Checks.FanBodyLambdaDispatcherConsumer
#print axioms Lamping.Checks.FanBodyLambdaDispatcherConsumer.actual_incoming
#print axioms Lamping.Checks.FanBodyLambdaDispatcherConsumer.full_samechain_dispatch
#print axioms Lamping.Checks.FanBodyLambdaDispatcherConsumer.actual_outer_pair
#print axioms Lamping.Checks.FanBodyLambdaDispatcherConsumer.actual_inner_pair
#print axioms Lamping.Checks.FanBodyLambdaDispatcherConsumer.actual_outer_supply
#print axioms Lamping.Checks.FanBodyLambdaDispatcherConsumer.actual_inner_supply
