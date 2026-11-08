import Lamping.Lamping.FanAppLambdaDispatcher
import Lamping.Checks.FanBodyFragmentTransportConsumer
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanAppLambdaDispatcherConsumer
open AG Graph Lambda Lambda.Labelled FanBodyDoubleLambdaReachable FanBodyDoubleLambdaParents
abbrev slotPosition (argument : Bool) : Position current.erase :=
  if argument then ⟨[.arg],rfl⟩ else ⟨[.fn],rfl⟩
abbrev slotEdges (argument : Bool) : List Path := if argument then [[.arg],[.fn]] else [[.fn]]
abbrev slotTerm (argument : Bool) : LTerm := if argument then FanBodyContextConsumer.argumentTerm else FanBodyContextConsumer.functionTerm
abbrev slotBody (argument : Bool) : LTerm := if argument then FanBodyContextConsumer.argumentBody else FanBodyContextConsumer.functionBody

def slotChain (argument : Bool) : PrerequisiteChain current (slotPosition argument).val (slotEdges argument) := by
  cases argument
  · exact .redex_lam (p:=[]) rfl
  · exact .lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl)

def fnOccurrence : SourceSubterm [] .external current [.fn] [] (.appFn current.label) FanBodyContextConsumer.functionTerm := .fn .nil
def argOccurrence : SourceSubterm [] .external current [.arg] [] (.appArg current.label) FanBodyContextConsumer.argumentTerm := .arg .nil

theorem slotLookup (argument : Bool) : current.subterm (slotPosition argument).val=
    some (.lam (slotTerm argument).label (slotBody argument)) := by cases argument <;> rfl

theorem actual_incoming {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B} (argument : Bool)
    (selection : OccurrenceFragmentSelection current g root) :
    ∃stamp,(selection (slotPosition argument)).context=.appFn stamp ∨
      (selection (slotPosition argument)).context=.appArg stamp := by
  cases argument
  · exact ⟨_,Or.inl ((selection (slotPosition false)).occurrence.same_occurrence fnOccurrence).2.1⟩
  · exact ⟨_,Or.inr ((selection (slotPosition true)).occurrence.same_occurrence argOccurrence).2.1⟩

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
/-- The FN case is a terminal ONE-edge chain. Both direct full-top calls use
only THIS n=0, no next-slot, parent/access/endpoint/Bool profile is supplied. -/
theorem full_samechain_dispatch (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site) (argument : Bool)
    (sourceFirst sourceSecond : OccurrenceFragmentSelection current site.net root)
    (targetFirst targetSecond : OccurrenceFragmentSelection current site.reduce root) :
    (sourceFirst (slotPosition argument)).fragment.segments=(sourceSecond (slotPosition argument)).fragment.segments ∧
      (targetFirst (slotPosition argument)).fragment.segments=(targetSecond (slotPosition argument)).fragment.segments := by
  have atSlot : (slotEdges argument)[0]?=some (slotPosition argument).val := by cases argument <;> rfl
  have forward := site.fan_app_lambda_same_slot_forward sourceMatches targetMatches flow positive principal
    sourceFirst (slotChain argument) (slotChain argument) rfl
    (slotPosition argument) (slotPosition argument) atSlot atSlot (slotLookup argument) (slotLookup argument)
    (actual_incoming argument sourceFirst) (actual_incoming argument sourceFirst)
    (targetFirst (slotPosition argument)) (targetSecond (slotPosition argument))
  have reflection := site.fan_app_lambda_same_slot_reflect sourceMatches targetMatches flow positive principal
    targetFirst (slotChain argument) (slotChain argument) rfl
    (slotPosition argument) (slotPosition argument) atSlot atSlot (slotLookup argument) (slotLookup argument)
    (actual_incoming argument targetFirst) (actual_incoming argument targetFirst)
    (sourceFirst (slotPosition argument)) (sourceSecond (slotPosition argument))
  exact ⟨reflection,forward⟩
end

theorem actual_outer_pair (principal : SiteActionPrincipal outerFan.site) (argument : Bool)
    (sourceFirst sourceSecond : OccurrenceFragmentSelection current outerFan.site.net (.inl ()))
    (targetFirst targetSecond : OccurrenceFragmentSelection current outerFan.site.reduce (.inl ())) :
    (sourceFirst (slotPosition argument)).fragment.segments=(sourceSecond (slotPosition argument)).fragment.segments ∧
      (targetFirst (slotPosition argument)).fragment.segments=(targetSecond (slotPosition argument)).fragment.segments := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  exact full_samechain_dispatch outerFan.site FanBodyOuterCutConsumer.source_matches FanBodyOuterCutConsumer.target_matches
    (outerFan.sourceIso.flowBalance flow) rfl principal argument sourceFirst sourceSecond targetFirst targetSecond

theorem actual_inner_pair (principal : SiteActionPrincipal innerFan.site) (argument : Bool)
    (sourceFirst sourceSecond : OccurrenceFragmentSelection current innerFan.site.net (.inl ()))
    (targetFirst targetSecond : OccurrenceFragmentSelection current innerFan.site.reduce (.inl ())) :
    (sourceFirst (slotPosition argument)).fragment.segments=(sourceSecond (slotPosition argument)).fragment.segments ∧
      (targetFirst (slotPosition argument)).fragment.segments=(targetSecond (slotPosition argument)).fragment.segments := by
  obtain ⟨flow,_,_,_,_⟩ := outer_certified
  exact full_samechain_dispatch innerFan.site actual_inner_source_matches actual_final_matches
    (innerFan.sourceIso.flowBalance flow) rfl principal argument sourceFirst sourceSecond targetFirst targetSecond

theorem actual_FN_ARG_chains :
    PrerequisiteChain current [.fn] [[.fn]] ∧PrerequisiteChain current [.arg] [[.arg],[.fn]] ∧
    (slotEdges false).length=1 ∧(slotEdges true).length=2 :=
  ⟨slotChain false,slotChain true,rfl,rfl⟩

/-- Real outer stage, original INIT/history, both literal incoming positions
and four arbitrary legal selectors. No claimed distinct-chain Joint truth. -/
theorem actual_outer_supply :
    INIT original ∧History [[]] original current ∧Closed original.erase ∧Closed current.erase ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet outerFan.site.reduce) [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    Matches outerFan.site.net (.inl ()) current.erase ∧Matches outerFan.site.reduce (.inl ()) current.erase ∧
    Nonempty (OccurrenceFragmentSelection current outerFan.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current outerFan.site.reduce (.inl ())) ∧
    (∀argument,PrerequisiteChain current (slotPosition argument).val (slotEdges argument)) ∧
    ∃_principal : SiteActionPrincipal outerFan.site,
      ∀ (argument : Bool) (sourceFirst sourceSecond : OccurrenceFragmentSelection current outerFan.site.net (.inl ()))
        (targetFirst targetSecond : OccurrenceFragmentSelection current outerFan.site.reduce (.inl ())),
        (sourceFirst (slotPosition argument)).fragment.segments=(sourceSecond (slotPosition argument)).fragment.segments ∧
        (targetFirst (slotPosition argument)).fragment.segments=(targetSecond (slotPosition argument)).fragment.segments := by
  refine ⟨FanBodyContextConsumer.initial,FanBodyContextConsumer.actualHistory,FanBodyContextConsumer.closed,
    FanBodyContextConsumer.targetClosed,.cons concrete.graph_step (.cons outerFan.graph_step (.refl _)),FanBodyOuterCutConsumer.source_matches,FanBodyOuterCutConsumer.target_matches,
    FanBodyOuterCutConsumer.source_matches.occurrence_fragment_selection FanBodyContextConsumer.targetClosed,
    FanBodyOuterCutConsumer.target_matches.occurrence_fragment_selection FanBodyContextConsumer.targetClosed,slotChain,?_⟩
  obtain ⟨principal⟩ := outerFan.site.actionPrincipal_exists
  exact ⟨principal,actual_outer_pair principal⟩

/-- Real inner stage, original INIT/history, both literal incoming positions
and four arbitrary legal selectors. No claimed distinct-chain Joint truth. -/
theorem actual_inner_supply :
    INIT original ∧History [[]] original current ∧Closed original.erase ∧Closed current.erase ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet innerFan.site.reduce) [.beta 0,.fanAction .lam 0 1 (by decide),.fanAction .lam 0 1 (by decide)] ∧
    Matches innerFan.site.net (.inl ()) current.erase ∧Matches innerFan.site.reduce (.inl ()) current.erase ∧
    Nonempty (OccurrenceFragmentSelection current innerFan.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current innerFan.site.reduce (.inl ())) ∧
    (∀argument,PrerequisiteChain current (slotPosition argument).val (slotEdges argument)) ∧
    ∃_principal : SiteActionPrincipal innerFan.site,
      ∀ (argument : Bool) (sourceFirst sourceSecond : OccurrenceFragmentSelection current innerFan.site.net (.inl ()))
        (targetFirst targetSecond : OccurrenceFragmentSelection current innerFan.site.reduce (.inl ())),
        (sourceFirst (slotPosition argument)).fragment.segments=(sourceSecond (slotPosition argument)).fragment.segments ∧
        (targetFirst (slotPosition argument)).fragment.segments=(targetSecond (slotPosition argument)).fragment.segments := by
  refine ⟨FanBodyContextConsumer.initial,FanBodyContextConsumer.actualHistory,FanBodyContextConsumer.closed,
    FanBodyContextConsumer.targetClosed,actual_three_step_trace,actual_inner_source_matches,actual_final_matches,
    actual_inner_source_matches.occurrence_fragment_selection FanBodyContextConsumer.targetClosed,
    actual_final_matches.occurrence_fragment_selection FanBodyContextConsumer.targetClosed,slotChain,?_⟩
  obtain ⟨principal⟩ := innerFan.site.actionPrincipal_exists
  exact ⟨principal,actual_inner_pair principal⟩
end Lamping.Checks.FanAppLambdaDispatcherConsumer
#print axioms Lamping.Checks.FanAppLambdaDispatcherConsumer.slotChain
#print axioms Lamping.Checks.FanAppLambdaDispatcherConsumer.slotLookup
#print axioms Lamping.Checks.FanAppLambdaDispatcherConsumer.actual_incoming
#print axioms Lamping.Checks.FanAppLambdaDispatcherConsumer.full_samechain_dispatch
#print axioms Lamping.Checks.FanAppLambdaDispatcherConsumer.actual_outer_pair
#print axioms Lamping.Checks.FanAppLambdaDispatcherConsumer.actual_inner_pair
#print axioms Lamping.Checks.FanAppLambdaDispatcherConsumer.actual_FN_ARG_chains
#print axioms Lamping.Checks.FanAppLambdaDispatcherConsumer.actual_outer_supply
#print axioms Lamping.Checks.FanAppLambdaDispatcherConsumer.actual_inner_supply
