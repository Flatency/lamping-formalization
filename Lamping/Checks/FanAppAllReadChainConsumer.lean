import Lamping.Lamping.FanAppChainRepresentationTransport
import Lamping.Checks.FanAppAllocatedChildReachable
import Lamping.Checks.FanAppArgumentLambdaConsumer
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanAppAllReadChainConsumer
open AG Graph Lambda Lambda.Labelled
namespace Allocated
open FanAppAllocatedChildReachable
open FanAppAllocatedChildReachable.Base
/-- Full natural high at the new genuine allocated APP incoming read.
The caller supplies no endpoint, Bool, parent path, role or nextslot. -/
theorem actual_all_read
    (principal : SiteActionPrincipal fanApp.site)
    (source : OccurrenceFragmentSelection current fanApp.site.net (.inl ()))
    (firstTarget secondTarget : OccurrenceFragmentSelection current fanApp.site.reduce (.inl ())) (branch : Bool) :
    (firstTarget (Syntax.innerPosition branch)).fragment.segments=
      (secondTarget (Syntax.innerPosition branch)).fragment.segments := by
  obtain ⟨flow,_,inputs,_,_⟩:=cro_certified
  exact fanApp.site.fan_app_all_read_same_slot_forward FanAppAllocatedChildReachable.actual_source_matches FanAppAllocatedChildReachable.actual_target_matches
    (fanApp.sourceIso.flowBalance flow) rfl (fanApp.sourceIso.rootInputs inputs) principal source
    (Syntax.actual_chain branch) (Syntax.actual_chain branch) rfl
    (Syntax.innerPosition branch) (Syntax.innerPosition branch)
    (Syntax.actual_read_slots branch).2.1 (Syntax.actual_read_slots branch).2.1
    (firstTarget (Syntax.innerPosition branch)) (secondTarget (Syntax.innerPosition branch))

/-- The entire ordered 5/6 READ image, with two honest target choices.
The generic whole transport uses ONE target selector; a second selector is
related only by the proved actual choice-independence theorem. -/
theorem actual_ordered_whole
    (principal : SiteActionPrincipal fanApp.site)
    (source : OccurrenceFragmentSelection current fanApp.site.net (.inl ()))
    (firstTarget secondTarget : OccurrenceFragmentSelection current fanApp.site.reduce (.inl ())) (branch : Bool) :
    canonicalChainImage firstTarget (Syntax.actual_chain branch)=
      canonicalChainImage secondTarget (Syntax.actual_chain branch) := by
  obtain ⟨flow,_,inputs,_,_⟩:=cro_certified
  have transported:=fanApp.site.fan_app_chain_representation_forward FanAppAllocatedChildReachable.actual_source_matches FanAppAllocatedChildReachable.actual_target_matches
    (fanApp.sourceIso.flowBalance flow) rfl (fanApp.sourceIso.rootInputs inputs) principal source firstTarget
    (Syntax.actual_chain branch) (Syntax.actual_chain branch) rfl
  exact transported.trans (canonicalChainImage_choice_independent FanAppAllocatedChildReachable.actual_target_matches firstTarget secondTarget (Syntax.actual_chain branch))

/-- Conditional non-identical chains are also accepted by the genuine
whole top. The SOURCE equality remains an explicit mathematical IH, not a
field or a claimed fact about distinct concrete chains. -/
theorem conditional_whole_forward
    (principal : SiteActionPrincipal fanApp.site)
    (source : OccurrenceFragmentSelection current fanApp.site.net (.inl ()))
    (target : OccurrenceFragmentSelection current fanApp.site.reduce (.inl ()))
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (sourceIH : SameChainRepresentation source first second) : SameChainRepresentation target first second := by
  obtain ⟨flow,_,inputs,_,_⟩:=cro_certified
  exact fanApp.site.fan_app_chain_representation_forward FanAppAllocatedChildReachable.actual_source_matches FanAppAllocatedChildReachable.actual_target_matches
    (fanApp.sourceIso.flowBalance flow) rfl (fanApp.sourceIso.rootInputs inputs) principal source target first second sourceIH

theorem actual_original_history_direct :
    INIT Syntax.original ∧Closed Syntax.original.erase ∧History [[.fn]] Syntax.original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet fanApp.site.reduce)
      [.beta 0,.fanAction .lam 0 1 (by decide),.fanAction .cro 0 1 (by decide),.fanAction .app 0 1 (by decide)] ∧
    Matches fanApp.site.net (.inl ()) current.erase ∧Matches fanApp.site.reduce (.inl ()) current.erase ∧
    Nonempty (OccurrenceFragmentSelection current fanApp.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current fanApp.site.reduce (.inl ())) ∧
    ∃_principal : SiteActionPrincipal fanApp.site,
      ∀(firstSource secondSource : OccurrenceFragmentSelection current fanApp.site.net (.inl ()))
       (firstTarget secondTarget : OccurrenceFragmentSelection current fanApp.site.reduce (.inl ())) (branch : Bool),
      canonicalChainImage firstSource (Syntax.actual_chain branch)=canonicalChainImage secondSource (Syntax.actual_chain branch) ∧
      (firstTarget (Syntax.innerPosition branch)).fragment.segments=(secondTarget (Syntax.innerPosition branch)).fragment.segments ∧
      canonicalChainImage firstTarget (Syntax.actual_chain branch)=canonicalChainImage secondTarget (Syntax.actual_chain branch) := by
  refine ⟨Syntax.initial,Syntax.sourceClosed,Syntax.actualHistory,actual_four_step_trace,
    FanAppAllocatedChildReachable.actual_source_matches,FanAppAllocatedChildReachable.actual_target_matches,
    FanAppAllocatedChildReachable.actual_source_matches.occurrence_fragment_selection Syntax.targetClosed,
    FanAppAllocatedChildReachable.actual_target_matches.occurrence_fragment_selection Syntax.targetClosed,?_⟩
  obtain ⟨principal⟩:=fanApp.site.actionPrincipal_exists
  refine ⟨principal,?_⟩
  intro firstSource secondSource firstTarget secondTarget branch
  exact ⟨canonicalChainImage_choice_independent FanAppAllocatedChildReachable.actual_source_matches firstSource secondSource (Syntax.actual_chain branch),
    actual_all_read principal firstSource firstTarget secondTarget branch,
    actual_ordered_whole principal firstSource firstTarget secondTarget branch⟩
end Allocated
namespace Earlier
open FanSuccessfulReachable FanAppSuccessfulReachable
open FanSuccessfulChains hiding original current
open FanLambdaChainPassageConsumer FanCurrentVariableBinderConsumer
open FanAppArgumentLambdaConsumer
/-- The earlier, genuinely different FUNCTION-var domain calls the same
complete allREAD top; its old natural microdomain theorem is not the call. -/
theorem actual_function_variable
    (principal : SiteActionPrincipal fanApp.site)
    (source : OccurrenceFragmentSelection current fanApp.site.net (.inl ()))
    (firstTarget secondTarget : OccurrenceFragmentSelection current fanApp.site.reduce (.inl ())) (branch : Bool) :
    (firstTarget (variablePosition branch)).fragment.segments=(secondTarget (variablePosition branch)).fragment.segments := by
  obtain ⟨flow,_,inputs,_,_⟩:=cro_certified
  exact fanApp.site.fan_app_all_read_same_slot_forward FanAppSuccessfulReachable.actual_source_matches
    FanAppSuccessfulReachable.actual_target_matches (fanApp.sourceIso.flowBalance flow) rfl
    (fanApp.sourceIso.rootInputs inputs) principal source (actualChain branch) (actualChain branch) rfl
    (variablePosition branch) (variablePosition branch) (actual_function_slots branch).2.1 (actual_function_slots branch).2.1
    (firstTarget (variablePosition branch)) (secondTarget (variablePosition branch))

/-- The actual ARG-lambda read and its 5/6-edge whole chain also consume
allREAD/whole directly, with the same original INIT/four-event carrier. -/
theorem actual_argument_lambda
    (principal : SiteActionPrincipal fanApp.site)
    (source : OccurrenceFragmentSelection current fanApp.site.net (.inl ()))
    (firstTarget secondTarget : OccurrenceFragmentSelection current fanApp.site.reduce (.inl ())) (branch : Bool) :
    (firstTarget (argumentPosition branch)).fragment.segments=(secondTarget (argumentPosition branch)).fragment.segments ∧
    canonicalChainImage firstTarget (argumentChain branch)=canonicalChainImage secondTarget (argumentChain branch) := by
  obtain ⟨flow,_,inputs,_,_⟩:=cro_certified
  have slot:=fanApp.site.fan_app_all_read_same_slot_forward FanAppSuccessfulReachable.actual_source_matches
    FanAppSuccessfulReachable.actual_target_matches (fanApp.sourceIso.flowBalance flow) rfl
    (fanApp.sourceIso.rootInputs inputs) principal source (argumentChain branch) (argumentChain branch) rfl
    (argumentPosition branch) (argumentPosition branch) (argument_slots branch).2.1 (argument_slots branch).2.1
    (firstTarget (argumentPosition branch)) (secondTarget (argumentPosition branch))
  have whole:=fanApp.site.fan_app_chain_representation_forward FanAppSuccessfulReachable.actual_source_matches
    FanAppSuccessfulReachable.actual_target_matches (fanApp.sourceIso.flowBalance flow) rfl
    (fanApp.sourceIso.rootInputs inputs) principal source firstTarget (argumentChain branch) (argumentChain branch) rfl
  exact ⟨slot,whole.trans (canonicalChainImage_choice_independent FanAppSuccessfulReachable.actual_target_matches firstTarget secondTarget (argumentChain branch))⟩
end Earlier
end Lamping.Checks.FanAppAllReadChainConsumer
#print axioms Lamping.AG.PathSite.fan_app_all_read_same_slot_forward
#print axioms Lamping.AG.PathSite.fan_app_chain_representation_forward
#print axioms Lamping.Checks.FanAppAllReadChainConsumer.Allocated.actual_all_read
#print axioms Lamping.Checks.FanAppAllReadChainConsumer.Allocated.actual_ordered_whole
#print axioms Lamping.Checks.FanAppAllReadChainConsumer.Allocated.conditional_whole_forward
#print axioms Lamping.Checks.FanAppAllReadChainConsumer.Allocated.actual_original_history_direct
#print axioms Lamping.Checks.FanAppAllReadChainConsumer.Earlier.actual_function_variable
#print axioms Lamping.Checks.FanAppAllReadChainConsumer.Earlier.actual_argument_lambda
