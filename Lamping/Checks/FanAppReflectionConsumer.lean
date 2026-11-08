import Lamping.Lamping.FanAppChainRepresentationReflection
import Lamping.Checks.FanAppAllocatedChildReachable
import Lamping.Checks.FanAppAllReadChainConsumer
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanAppReflectionConsumer
open AG Graph Lambda Lambda.Labelled
open FanAppAllocatedChildReachable
open FanAppAllocatedChildReachable.Base

/-- The actual allocated APP READ calls the entire natural reflection top.
TARGET IH is the honest samechain reflexive equality, not distinct REP truth. -/
theorem actual_slot_reflection
    (principal : SiteActionPrincipal fanApp.site)
    (firstSource secondSource : OccurrenceFragmentSelection current fanApp.site.net (.inl ()))
    (target : OccurrenceFragmentSelection current fanApp.site.reduce (.inl ())) (branch : Bool) :
    (firstSource (Syntax.innerPosition branch)).fragment.segments=
      (secondSource (Syntax.innerPosition branch)).fragment.segments := by
  obtain ⟨flow,_,inputs,_,_⟩:=cro_certified
  exact fanApp.site.fan_app_all_read_same_slot_reflect
    FanAppAllocatedChildReachable.actual_source_matches FanAppAllocatedChildReachable.actual_target_matches
    (fanApp.sourceIso.flowBalance flow) rfl (fanApp.sourceIso.rootInputs inputs) principal target
    (Syntax.actual_chain branch) (Syntax.actual_chain branch) rfl
    (Syntax.innerPosition branch) (Syntax.innerPosition branch)
    (Syntax.actual_read_slots branch).2.1 (Syntax.actual_read_slots branch).2.1
    (firstSource (Syntax.innerPosition branch)) (secondSource (Syntax.innerPosition branch))

/-- Actual whole reflection is called before explicit cross-choice transport. -/
theorem actual_ordered_reflection
    (principal : SiteActionPrincipal fanApp.site)
    (firstSource secondSource : OccurrenceFragmentSelection current fanApp.site.net (.inl ()))
    (target : OccurrenceFragmentSelection current fanApp.site.reduce (.inl ())) (branch : Bool) :
    canonicalChainImage firstSource (Syntax.actual_chain branch)=
      canonicalChainImage secondSource (Syntax.actual_chain branch) := by
  obtain ⟨flow,_,inputs,_,_⟩:=cro_certified
  have reflected:=fanApp.site.fan_app_chain_representation_reflect
    FanAppAllocatedChildReachable.actual_source_matches FanAppAllocatedChildReachable.actual_target_matches
    (fanApp.sourceIso.flowBalance flow) rfl (fanApp.sourceIso.rootInputs inputs) principal firstSource target
    (Syntax.actual_chain branch) (Syntax.actual_chain branch) rfl
  exact reflected.trans (canonicalChainImage_choice_independent
    FanAppAllocatedChildReachable.actual_source_matches firstSource secondSource (Syntax.actual_chain branch))

/-- The complete ordered reverse accepts the real TARGET mathematical IH
for arbitrary supplied successful chains; this theorem does not assert it. -/
theorem conditional_whole_reflection
    (principal : SiteActionPrincipal fanApp.site)
    (source : OccurrenceFragmentSelection current fanApp.site.net (.inl ()))
    (target : OccurrenceFragmentSelection current fanApp.site.reduce (.inl ()))
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (targetIH : SameChainRepresentation target first second) : SameChainRepresentation source first second := by
  obtain ⟨flow,_,inputs,_,_⟩:=cro_certified
  exact fanApp.site.fan_app_chain_representation_reflect
    FanAppAllocatedChildReachable.actual_source_matches FanAppAllocatedChildReachable.actual_target_matches
    (fanApp.sourceIso.flowBalance flow) rfl (fanApp.sourceIso.rootInputs inputs) principal source target first second targetIH

/-- SOURCE chain invariance is a conditional induction hypothesis; no actual
invariance, auxiliary clause or SOURCE/target Joint truth is manufactured. -/
theorem conditional_chain_invariant
    (principal : SiteActionPrincipal fanApp.site)
    (source : OccurrenceFragmentSelection current fanApp.site.net (.inl ()))
    (target : OccurrenceFragmentSelection current fanApp.site.reduce (.inl ()))
    (sourceIH : ChainRepresentationInvariant Syntax.targetClosed source) :
    ChainRepresentationInvariant Syntax.targetClosed target := by
  obtain ⟨flow,_,inputs,_,_⟩:=cro_certified
  exact fanApp.site.fan_app_chain_invariant_preserve
    FanAppAllocatedChildReachable.actual_source_matches FanAppAllocatedChildReachable.actual_target_matches
    (fanApp.sourceIso.flowBalance flow) rfl (fanApp.sourceIso.rootInputs inputs) principal
    Syntax.targetClosed source target sourceIH

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
      (firstSource (Syntax.innerPosition branch)).fragment.segments=(secondSource (Syntax.innerPosition branch)).fragment.segments ∧
      canonicalChainImage firstTarget (Syntax.actual_chain branch)=canonicalChainImage secondTarget (Syntax.actual_chain branch) := by
  refine ⟨Syntax.initial,Syntax.sourceClosed,Syntax.actualHistory,actual_four_step_trace,
    FanAppAllocatedChildReachable.actual_source_matches,FanAppAllocatedChildReachable.actual_target_matches,
    FanAppAllocatedChildReachable.actual_source_matches.occurrence_fragment_selection Syntax.targetClosed,
    FanAppAllocatedChildReachable.actual_target_matches.occurrence_fragment_selection Syntax.targetClosed,?_⟩
  obtain ⟨principal⟩:=fanApp.site.actionPrincipal_exists
  refine ⟨principal,?_⟩
  intro firstSource secondSource firstTarget secondTarget branch
  exact ⟨actual_ordered_reflection principal firstSource secondSource firstTarget branch,
    actual_slot_reflection principal firstSource secondSource firstTarget branch,
    canonicalChainImage_choice_independent FanAppAllocatedChildReachable.actual_target_matches
      firstTarget secondTarget (Syntax.actual_chain branch)⟩

namespace Earlier
open FanSuccessfulReachable FanAppSuccessfulReachable
open FanSuccessfulChains hiding original current
open FanLambdaChainPassageConsumer FanCurrentVariableBinderConsumer
open FanAppArgumentLambdaConsumer

theorem actual_function_variable_reflection
    (principal : SiteActionPrincipal FanAppSuccessfulReachable.fanApp.site)
    (firstSource secondSource : OccurrenceFragmentSelection FanSuccessfulReachable.current FanAppSuccessfulReachable.fanApp.site.net (.inl ()))
    (target : OccurrenceFragmentSelection FanSuccessfulReachable.current FanAppSuccessfulReachable.fanApp.site.reduce (.inl ())) (branch : Bool) :
    (firstSource (variablePosition branch)).fragment.segments=(secondSource (variablePosition branch)).fragment.segments := by
  obtain ⟨flow,_,inputs,_,_⟩:=FanSuccessfulReachable.cro_certified
  exact FanAppSuccessfulReachable.fanApp.site.fan_app_all_read_same_slot_reflect FanAppSuccessfulReachable.actual_source_matches
    FanAppSuccessfulReachable.actual_target_matches (FanAppSuccessfulReachable.fanApp.sourceIso.flowBalance flow) rfl
    (FanAppSuccessfulReachable.fanApp.sourceIso.rootInputs inputs) principal target (actualChain branch) (actualChain branch) rfl
    (variablePosition branch) (variablePosition branch) (actual_function_slots branch).2.1 (actual_function_slots branch).2.1
    (firstSource (variablePosition branch)) (secondSource (variablePosition branch))

theorem actual_argument_lambda_reflection
    (principal : SiteActionPrincipal FanAppSuccessfulReachable.fanApp.site)
    (firstSource secondSource : OccurrenceFragmentSelection FanSuccessfulReachable.current FanAppSuccessfulReachable.fanApp.site.net (.inl ()))
    (target : OccurrenceFragmentSelection FanSuccessfulReachable.current FanAppSuccessfulReachable.fanApp.site.reduce (.inl ())) (branch : Bool) :
    (firstSource (argumentPosition branch)).fragment.segments=(secondSource (argumentPosition branch)).fragment.segments ∧
    canonicalChainImage firstSource (argumentChain branch)=canonicalChainImage secondSource (argumentChain branch) := by
  obtain ⟨flow,_,inputs,_,_⟩:=FanSuccessfulReachable.cro_certified
  have slot:=FanAppSuccessfulReachable.fanApp.site.fan_app_all_read_same_slot_reflect FanAppSuccessfulReachable.actual_source_matches
    FanAppSuccessfulReachable.actual_target_matches (FanAppSuccessfulReachable.fanApp.sourceIso.flowBalance flow) rfl
    (FanAppSuccessfulReachable.fanApp.sourceIso.rootInputs inputs) principal target (argumentChain branch) (argumentChain branch) rfl
    (argumentPosition branch) (argumentPosition branch) (argument_slots branch).2.1 (argument_slots branch).2.1
    (firstSource (argumentPosition branch)) (secondSource (argumentPosition branch))
  have whole:=FanAppSuccessfulReachable.fanApp.site.fan_app_chain_representation_reflect FanAppSuccessfulReachable.actual_source_matches
    FanAppSuccessfulReachable.actual_target_matches (FanAppSuccessfulReachable.fanApp.sourceIso.flowBalance flow) rfl
    (FanAppSuccessfulReachable.fanApp.sourceIso.rootInputs inputs) principal firstSource target (argumentChain branch) (argumentChain branch) rfl
  exact ⟨slot,whole.trans (canonicalChainImage_choice_independent FanAppSuccessfulReachable.actual_source_matches firstSource secondSource (argumentChain branch))⟩
end Earlier
end Lamping.Checks.FanAppReflectionConsumer
#print axioms Lamping.AG.PathSite.fan_app_all_read_same_slot_reflect
#print axioms Lamping.AG.PathSite.fan_app_chain_representation_reflect
#print axioms Lamping.AG.PathSite.fan_app_chain_invariant_preserve
#print axioms Lamping.Checks.FanAppReflectionConsumer.actual_slot_reflection
#print axioms Lamping.Checks.FanAppReflectionConsumer.actual_ordered_reflection
#print axioms Lamping.Checks.FanAppReflectionConsumer.conditional_whole_reflection
#print axioms Lamping.Checks.FanAppReflectionConsumer.conditional_chain_invariant
#print axioms Lamping.Checks.FanAppReflectionConsumer.actual_original_history_direct
-- The genuine copied-child/kept-parent KC domain and 5/6-chain certificate
-- is the accepted formal supplier, not a newly reconstructed carrier.
#print axioms Lamping.Checks.FanAppAllocatedChildReachable.Domain.actual_reachable_allocated_child
#print axioms Lamping.Checks.FanAppReflectionConsumer.Earlier.actual_function_variable_reflection
#print axioms Lamping.Checks.FanAppReflectionConsumer.Earlier.actual_argument_lambda_reflection
