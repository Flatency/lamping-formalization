import Lamping.Lamping.FanLambdaContextFragmentTransport
import Lamping.Checks.FanLambdaSlotSynchronization
namespace Lamping.Checks.FanLambdaContextFragmentConsumer
open AG Graph Lambda Lambda.Labelled FanSuccessfulReachable
open FanSuccessfulChains hiding current original
open FanLambdaChainPassageConsumer
/-- The source occurrence itself has the actual ARG incoming port. This is
not a FUNCTION claim and not a supplied physical-parent profile. -/
theorem actual_arg_incoming
    (source : OccurrenceFragmentSelection current sourceNet (.inl ())) (branch : Bool) :
    (source (selectedPosition branch)).context=.appArg (if branch then .atom 4 else .atom 5) := by
  cases branch
  · exact ((source (selectedPosition false)).occurrence.same_occurrence left_lambda_occurrence).2.1
  · exact ((source (selectedPosition true)).occurrence.same_occurrence right_lambda_occurrence).2.1

/-- Independent actual lambda paths identify any chosen occurrence access
at THIS word; no copied finish is an oracle supplied by the consumer. -/
theorem actual_context_finish
    (target : OccurrenceFragmentSelection current targetNet (.inl ())) (branch : Bool) :
    (target (selectedPosition branch)).fragment.access.val.getLast?=
      some (targetNet.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)) := by
  have same : (target (selectedPosition branch)).fragment.access=
      SuccessfulAuxiliaryPhysicalPair.chosenParent branch :=
    FanLambdaChainPassageConsumer.actual_target_matches.accessWord_injective
      ((target (selectedPosition branch)).fragment.word.trans (SuccessfulAuxiliaryPhysicalPair.chosenWord branch).symm)
  rw [same]
  exact SuccessfulAuxiliaryPhysicalPair.chosenFinish branch

/-- Direct full-core use at noninitial slot one of the genuine whole chain.
All parent accesses and kept APP endpoints are derived inside the producer. -/
theorem actual_successful_context_forward
    (principal : SiteActionPrincipal actualFanPresentation.site)
    (source : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (firstTarget secondTarget : OccurrenceFragmentSelection current targetNet (.inl ())) (branch : Bool) :
    (firstTarget (selectedPosition branch)).fragment.segments=
      (secondTarget (selectedPosition branch)).fragment.segments := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  exact actualFanPresentation.site.fan_lambda_context_same_slot_fragment_forward
    FanLambdaChainPassageConsumer.actual_source_matches FanLambdaChainPassageConsumer.actual_target_matches
    (actualFanPresentation.sourceIso.flowBalance flow) rfl principal source
    (actualChain branch) (actualChain branch) rfl (selectedPosition branch) (selectedPosition branch)
    (FanLambdaSlotSynchronizationConsumer.actual_slot branch) (FanLambdaSlotSynchronizationConsumer.actual_slot branch)
    ⟨_,Or.inr (actual_arg_incoming source branch)⟩ ⟨_,Or.inr (actual_arg_incoming source branch)⟩
    (firstTarget (selectedPosition branch)) (secondTarget (selectedPosition branch)) branch branch
    (actual_context_finish firstTarget branch) (actual_context_finish secondTarget branch)

/-- Only a conditional source Joint wrapper is consumed; no actual Joint
truth or preservation of all fan cases is asserted. -/
theorem actual_conditional_joint_context_forward
    (principal : SiteActionPrincipal actualFanPresentation.site)
    (source : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (joint : JointRepresentation targetClosed source)
    (firstTarget secondTarget : OccurrenceFragmentSelection current targetNet (.inl ())) (branch : Bool) :
    (firstTarget (selectedPosition branch)).fragment.segments=
      (secondTarget (selectedPosition branch)).fragment.segments := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  exact actualFanPresentation.site.fan_lambda_context_joint_same_slot_fragment_forward
    FanLambdaChainPassageConsumer.actual_source_matches FanLambdaChainPassageConsumer.actual_target_matches
    (actualFanPresentation.sourceIso.flowBalance flow) rfl principal targetClosed source joint
    (actualChain branch) (actualChain branch) ⟨ChainIncidenceIso.refl _⟩
    (selectedPosition branch) (selectedPosition branch)
    (FanLambdaSlotSynchronizationConsumer.actual_slot branch) (FanLambdaSlotSynchronizationConsumer.actual_slot branch)
    ⟨_,Or.inr (actual_arg_incoming source branch)⟩ ⟨_,Or.inr (actual_arg_incoming source branch)⟩
    (firstTarget (selectedPosition branch)) (secondTarget (selectedPosition branch)) branch branch
    (actual_context_finish firstTarget branch) (actual_context_finish secondTarget branch)

/-- Actual sameINIT/history/two GraphSteps, nonempty choices and successful
4/5-edge whole chains with genuine slot1 ARG-lambda reads. The incoming ARG
classification is supplied from actual syntax, not imposed on all lambda slots. -/
theorem actual_reachable_context_fragment_transport :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet targetNet)
      [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    Matches sourceNet (.inl ()) current.erase ∧Matches targetNet (.inl ()) current.erase ∧
    Closed current.erase ∧
    Nonempty (OccurrenceFragmentSelection current sourceNet (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current targetNet (.inl ())) ∧
    ∃ principal : SiteActionPrincipal actualFanPresentation.site,
      ∀ (firstSource secondSource : OccurrenceFragmentSelection current sourceNet (.inl ()))
        (firstTarget secondTarget : OccurrenceFragmentSelection current targetNet (.inl ())) (branch : Bool),
        PrerequisiteChain current (starting branch) (fullEdges branch) ∧
        (fullEdges branch).length=(if branch then 5 else 4) ∧
        (fullEdges branch)[1]?=some (selected branch) ∧
        PrerequisiteChain current (selected branch) (remainingEdges branch) ∧
        (firstSource (selectedPosition branch)).context=.appArg (if branch then .atom 4 else .atom 5) ∧
        (firstSource (selectedPosition branch)).fragment.segments=
          (secondSource (selectedPosition branch)).fragment.segments ∧
        (firstTarget (selectedPosition branch)).fragment.segments=
          (secondTarget (selectedPosition branch)).fragment.segments := by
  refine ⟨FanSuccessfulChains.initial,sourceClosed,actualHistory,
    FanLambdaChainPassageConsumer.actual_two_step_trace,
    FanLambdaChainPassageConsumer.actual_source_matches,FanLambdaChainPassageConsumer.actual_target_matches,
    targetClosed,
    FanLambdaChainPassageConsumer.actual_source_matches.occurrence_fragment_selection targetClosed,
    FanLambdaChainPassageConsumer.actual_target_matches.occurrence_fragment_selection targetClosed,?_⟩
  obtain ⟨principal⟩ := actualFanPresentation.site.actionPrincipal_exists
  refine ⟨principal,?_⟩
  intro firstSource secondSource firstTarget secondTarget branch
  exact ⟨actualChain branch,(by cases branch <;> rfl),
    FanLambdaSlotSynchronizationConsumer.actual_slot branch,actualRemainder branch,
    actual_arg_incoming firstSource branch,
    OccurrenceFragment.segments_unique FanLambdaChainPassageConsumer.actual_source_matches _ _,
    actual_successful_context_forward principal firstSource firstTarget secondTarget branch⟩
#print axioms PathSite.fan_lambda_context_canonical_trim
#print axioms SourceEdgeFragment.fan_kept_parent_copied_context_cut
#print axioms SourceEdgeFragment.fan_kept_parent_copied_context_forward
#print axioms OccurrenceFragment.app_incoming_parent
#print axioms PathSite.fan_lambda_context_same_slot_fragment_forward
#print axioms PathSite.fan_lambda_context_joint_same_slot_fragment_forward
#print axioms actual_arg_incoming
#print axioms actual_context_finish
#print axioms actual_successful_context_forward
#print axioms actual_conditional_joint_context_forward
#print axioms actual_reachable_context_fragment_transport
end Lamping.Checks.FanLambdaContextFragmentConsumer
