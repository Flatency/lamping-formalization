import Lamping.Lamping.FanProperSlotDispatcher
import Lamping.Checks.FanAppLambdaDispatcherConsumer
import Lamping.Checks.FanBodyLambdaDispatcherConsumer
import Lamping.Checks.FanSuccessfulReachable
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanProperSlotDispatcherConsumer
open AG Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
/-- Four actual choices call both COMPLETE proper tops; samechain reflexivity
is real but does not assert a distinct-chain or Joint invariant. -/
theorem proper_four_choices (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true) (principal : SiteActionPrincipal site)
    (chain : PrerequisiteChain current start edges) (position : Position current.erase)
    {n : Nat} (slot : edges[n]?=some position.val)
    (proper : (∃stamp fn arg,current.subterm position.val=some (.app stamp fn arg)) ∨
      (∃stamp body,current.subterm position.val=some (.lam stamp body)))
    (sourceFirst sourceSecond : OccurrenceFragmentSelection current site.net root)
    (targetFirst targetSecond : OccurrenceFragmentSelection current site.reduce root) :
    (sourceFirst position).fragment.segments=(sourceSecond position).fragment.segments ∧
      (targetFirst position).fragment.segments=(targetSecond position).fragment.segments := by
  have forward := site.fan_proper_same_slot_forward sourceMatches targetMatches flow positive principal
    sourceFirst chain chain rfl position position slot slot proper proper (targetFirst position) (targetSecond position)
  have reflection := site.fan_proper_same_slot_reflect sourceMatches targetMatches flow positive principal
    targetFirst chain chain rfl position position slot slot proper proper (sourceFirst position) (sourceSecond position)
  exact ⟨reflection,forward⟩

/-- APP reads directly consume their specialized tops AND the complete
proper tops, at the supplied real commonordinal, with no incoming profile. -/
theorem app_four_choices (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true) (principal : SiteActionPrincipal site)
    (chain : PrerequisiteChain current start edges) (position : Position current.erase)
    {n : Nat} (slot : edges[n]?=some position.val)
    (lookup : current.subterm position.val=some (.app stamp fn arg))
    (sourceFirst sourceSecond : OccurrenceFragmentSelection current site.net root)
    (targetFirst targetSecond : OccurrenceFragmentSelection current site.reduce root) :
    ((sourceFirst position).fragment.segments=(sourceSecond position).fragment.segments ∧
      (targetFirst position).fragment.segments=(targetSecond position).fragment.segments) ∧
    ((sourceFirst position).fragment.segments=(sourceSecond position).fragment.segments ∧
      (targetFirst position).fragment.segments=(targetSecond position).fragment.segments) := by
  have forward := site.fan_app_read_same_slot_forward sourceMatches targetMatches flow positive principal
    sourceFirst chain chain rfl position position slot slot lookup lookup (targetFirst position) (targetSecond position)
  have reflection := site.fan_app_read_same_slot_reflect sourceMatches targetMatches flow positive principal
    targetFirst chain chain rfl position position slot slot lookup lookup (sourceFirst position) (sourceSecond position)
  exact ⟨⟨reflection,forward⟩,proper_four_choices site sourceMatches targetMatches flow positive principal
    chain position slot (Or.inl ⟨_,_,_,lookup⟩) sourceFirst sourceSecond targetFirst targetSecond⟩
end
namespace App
open FanSuccessfulReachable
open FanSuccessfulChains hiding current original
abbrev position : Position current.erase := ⟨[.fn,.body,.fn],rfl⟩
abbrev readStart (shifted : Bool) : Path := if shifted then rightBody else right
abbrev readEdges (shifted : Bool) : List Path := if shifted then rightBodyEdges else rightEdges
abbrev ordinal (shifted : Bool) : Nat := if shifted then 2 else 1

def actualChain (shifted : Bool) : PrerequisiteChain current (readStart shifted) (readEdges shifted) := by
  cases shifted
  · exact right_lambda_chain
  · exact right_body_chain

theorem actualSlot (shifted : Bool) : (readEdges shifted)[ordinal shifted]?=some position.val := by cases shifted <;> rfl

theorem actualLookup : current.subterm position.val=
    some (.app (.atom 5) (.var (.atom 6) 0) (.lam leftLabel callerBody)) := rfl

theorem source_matches : Matches actualFanPresentation.site.net (.inl ()) current.erase :=
  actualFanPresentation.sourceIso.matches beta_matches

theorem target_matches : Matches actualFanPresentation.site.reduce (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := lambda_certified;exact matching

/-- The site is the FIRST fan-lambda action, not the later control fan. -/
theorem actual_pair (principal : SiteActionPrincipal actualFanPresentation.site) (shifted : Bool)
    (sourceFirst sourceSecond : OccurrenceFragmentSelection current actualFanPresentation.site.net (.inl ()))
    (targetFirst targetSecond : OccurrenceFragmentSelection current actualFanPresentation.site.reduce (.inl ())) :
    ((sourceFirst position).fragment.segments=(sourceSecond position).fragment.segments ∧
      (targetFirst position).fragment.segments=(targetSecond position).fragment.segments) ∧
    ((sourceFirst position).fragment.segments=(sourceSecond position).fragment.segments ∧
      (targetFirst position).fragment.segments=(targetSecond position).fragment.segments) := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  exact app_four_choices actualFanPresentation.site source_matches target_matches
    (actualFanPresentation.sourceIso.flowBalance flow) rfl principal (actualChain shifted) position (actualSlot shifted)
    actualLookup sourceFirst sourceSecond targetFirst targetSecond

theorem actual_supply :
    INIT original ∧History [[.fn]] original current ∧Closed original.erase ∧Closed current.erase ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet actualFanPresentation.site.reduce)
      [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    Matches actualFanPresentation.site.net (.inl ()) current.erase ∧Matches actualFanPresentation.site.reduce (.inl ()) current.erase ∧
    Nonempty (OccurrenceFragmentSelection current actualFanPresentation.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current actualFanPresentation.site.reduce (.inl ())) ∧
    (readEdges false).length=4 ∧(readEdges true).length=5 ∧ordinal false=1 ∧ordinal true=2 ∧
    (∀shifted,PrerequisiteChain current (readStart shifted) (readEdges shifted)) ∧
    ∃_principal : SiteActionPrincipal actualFanPresentation.site,
      ∀ (_shifted : Bool)
        (sourceFirst sourceSecond : OccurrenceFragmentSelection current actualFanPresentation.site.net (.inl ()))
        (targetFirst targetSecond : OccurrenceFragmentSelection current actualFanPresentation.site.reduce (.inl ())),
        ((sourceFirst position).fragment.segments=(sourceSecond position).fragment.segments ∧
          (targetFirst position).fragment.segments=(targetSecond position).fragment.segments) ∧
        ((sourceFirst position).fragment.segments=(sourceSecond position).fragment.segments ∧
          (targetFirst position).fragment.segments=(targetSecond position).fragment.segments) := by
  refine ⟨initial,actualHistory,sourceClosed,targetClosed,
    .cons concrete.graph_step (.cons actualFanPresentation.graph_step (.refl _)),source_matches,target_matches,
    source_matches.occurrence_fragment_selection targetClosed,target_matches.occurrence_fragment_selection targetClosed,
    rfl,rfl,rfl,rfl,actualChain,?_⟩
  obtain ⟨principal⟩ := actualFanPresentation.site.actionPrincipal_exists
  exact ⟨principal,actual_pair principal⟩
end App
namespace K
open FanBodyDoubleLambdaReachable
abbrev position (choice : Bool⊕Unit) : Position current.erase := match choice with
  | .inl argument => FanAppLambdaDispatcherConsumer.slotPosition argument
  | .inr () => FanBodyLambdaDispatcherConsumer.bodyPosition
abbrev readEdges (choice : Bool⊕Unit) : List Path := match choice with
  | .inl argument => FanAppLambdaDispatcherConsumer.slotEdges argument
  | .inr () => FanBodyContextConsumer.leftEdges
abbrev readStart (choice : Bool⊕Unit) : Path := (position choice).val

def actualChain (choice : Bool⊕Unit) : PrerequisiteChain current (readStart choice) (readEdges choice) := by
  cases choice with
  | inl argument => exact FanAppLambdaDispatcherConsumer.slotChain argument
  | inr u => cases u;exact FanBodyContextConsumer.leftChain

theorem actualSlot (choice : Bool⊕Unit) : (readEdges choice)[0]?=some (position choice).val := by
  cases choice with
  | inl argument => cases argument <;> rfl
  | inr u => cases u;rfl

theorem actualProper (choice : Bool⊕Unit) :
    (∃stamp fn arg,current.subterm (position choice).val=some (.app stamp fn arg)) ∨
    (∃stamp body,current.subterm (position choice).val=some (.lam stamp body)) := by
  cases choice with
  | inl argument => exact Or.inr ⟨_,_,FanAppLambdaDispatcherConsumer.slotLookup argument⟩
  | inr u => cases u;exact Or.inr ⟨_,_,rfl⟩

theorem actual_outer_pair (principal : SiteActionPrincipal outerFan.site) (choice : Bool⊕Unit)
    (sourceFirst sourceSecond : OccurrenceFragmentSelection current outerFan.site.net (.inl ()))
    (targetFirst targetSecond : OccurrenceFragmentSelection current outerFan.site.reduce (.inl ())) :
    (sourceFirst (position choice)).fragment.segments=(sourceSecond (position choice)).fragment.segments ∧
      (targetFirst (position choice)).fragment.segments=(targetSecond (position choice)).fragment.segments := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  exact proper_four_choices outerFan.site FanBodyOuterCutConsumer.source_matches FanBodyOuterCutConsumer.target_matches
    (outerFan.sourceIso.flowBalance flow) rfl principal (actualChain choice) (position choice) (actualSlot choice)
    (actualProper choice) sourceFirst sourceSecond targetFirst targetSecond

theorem actual_outer_supply :
    INIT original ∧History [[]] original current ∧Closed original.erase ∧Closed current.erase ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet outerFan.site.reduce) [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    Matches outerFan.site.net (.inl ()) current.erase ∧Matches outerFan.site.reduce (.inl ()) current.erase ∧
    Nonempty (OccurrenceFragmentSelection current outerFan.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current outerFan.site.reduce (.inl ())) ∧
    (∀choice,PrerequisiteChain current (readStart choice) (readEdges choice)) ∧
    ∃_principal : SiteActionPrincipal outerFan.site,
      ∀ (choice : Bool⊕Unit) (sourceFirst sourceSecond : OccurrenceFragmentSelection current outerFan.site.net (.inl ()))
        (targetFirst targetSecond : OccurrenceFragmentSelection current outerFan.site.reduce (.inl ())),
        (sourceFirst (position choice)).fragment.segments=(sourceSecond (position choice)).fragment.segments ∧
          (targetFirst (position choice)).fragment.segments=(targetSecond (position choice)).fragment.segments := by
  refine ⟨FanBodyContextConsumer.initial,FanBodyContextConsumer.actualHistory,FanBodyContextConsumer.closed,
    FanBodyContextConsumer.targetClosed,.cons concrete.graph_step (.cons outerFan.graph_step (.refl _)),FanBodyOuterCutConsumer.source_matches,FanBodyOuterCutConsumer.target_matches,
    FanBodyOuterCutConsumer.source_matches.occurrence_fragment_selection FanBodyContextConsumer.targetClosed,
    FanBodyOuterCutConsumer.target_matches.occurrence_fragment_selection FanBodyContextConsumer.targetClosed,actualChain,?_⟩
  obtain ⟨principal⟩ := outerFan.site.actionPrincipal_exists
  exact ⟨principal,actual_outer_pair principal⟩

theorem actual_inner_pair (principal : SiteActionPrincipal innerFan.site) (choice : Bool⊕Unit)
    (sourceFirst sourceSecond : OccurrenceFragmentSelection current innerFan.site.net (.inl ()))
    (targetFirst targetSecond : OccurrenceFragmentSelection current innerFan.site.reduce (.inl ())) :
    (sourceFirst (position choice)).fragment.segments=(sourceSecond (position choice)).fragment.segments ∧
      (targetFirst (position choice)).fragment.segments=(targetSecond (position choice)).fragment.segments := by
  obtain ⟨flow,_,_,_,_⟩ := outer_certified
  exact proper_four_choices innerFan.site actual_inner_source_matches actual_final_matches
    (innerFan.sourceIso.flowBalance flow) rfl principal (actualChain choice) (position choice) (actualSlot choice)
    (actualProper choice) sourceFirst sourceSecond targetFirst targetSecond

theorem actual_inner_supply :
    INIT original ∧History [[]] original current ∧Closed original.erase ∧Closed current.erase ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet innerFan.site.reduce) [.beta 0,.fanAction .lam 0 1 (by decide),.fanAction .lam 0 1 (by decide)] ∧
    Matches innerFan.site.net (.inl ()) current.erase ∧Matches innerFan.site.reduce (.inl ()) current.erase ∧
    Nonempty (OccurrenceFragmentSelection current innerFan.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current innerFan.site.reduce (.inl ())) ∧
    (∀choice,PrerequisiteChain current (readStart choice) (readEdges choice)) ∧
    ∃_principal : SiteActionPrincipal innerFan.site,
      ∀ (choice : Bool⊕Unit) (sourceFirst sourceSecond : OccurrenceFragmentSelection current innerFan.site.net (.inl ()))
        (targetFirst targetSecond : OccurrenceFragmentSelection current innerFan.site.reduce (.inl ())),
        (sourceFirst (position choice)).fragment.segments=(sourceSecond (position choice)).fragment.segments ∧
          (targetFirst (position choice)).fragment.segments=(targetSecond (position choice)).fragment.segments := by
  refine ⟨FanBodyContextConsumer.initial,FanBodyContextConsumer.actualHistory,FanBodyContextConsumer.closed,
    FanBodyContextConsumer.targetClosed,actual_three_step_trace,actual_inner_source_matches,actual_final_matches,
    actual_inner_source_matches.occurrence_fragment_selection FanBodyContextConsumer.targetClosed,
    actual_final_matches.occurrence_fragment_selection FanBodyContextConsumer.targetClosed,actualChain,?_⟩
  obtain ⟨principal⟩ := innerFan.site.actionPrincipal_exists
  exact ⟨principal,actual_inner_pair principal⟩
end K
end Lamping.Checks.FanProperSlotDispatcherConsumer
#print axioms Lamping.Checks.FanProperSlotDispatcherConsumer.proper_four_choices
#print axioms Lamping.Checks.FanProperSlotDispatcherConsumer.app_four_choices
#print axioms Lamping.Checks.FanProperSlotDispatcherConsumer.App.actualChain
#print axioms Lamping.Checks.FanProperSlotDispatcherConsumer.App.actualSlot
#print axioms Lamping.Checks.FanProperSlotDispatcherConsumer.App.actualLookup
#print axioms Lamping.Checks.FanProperSlotDispatcherConsumer.App.source_matches
#print axioms Lamping.Checks.FanProperSlotDispatcherConsumer.App.target_matches
#print axioms Lamping.Checks.FanProperSlotDispatcherConsumer.App.actual_pair
#print axioms Lamping.Checks.FanProperSlotDispatcherConsumer.App.actual_supply
#print axioms Lamping.Checks.FanProperSlotDispatcherConsumer.K.actualProper
#print axioms Lamping.Checks.FanProperSlotDispatcherConsumer.K.actual_outer_pair
#print axioms Lamping.Checks.FanProperSlotDispatcherConsumer.K.actual_inner_pair
#print axioms Lamping.Checks.FanProperSlotDispatcherConsumer.K.actual_outer_supply
#print axioms Lamping.Checks.FanProperSlotDispatcherConsumer.K.actual_inner_supply
