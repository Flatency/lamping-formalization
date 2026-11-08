import Lamping.Lamping.FanLambdaSlotSynchronization
import Lamping.Checks.FanLambdaChainPassages
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanLambdaSlotSynchronizationConsumer
open AG Graph Lambda Lambda.Labelled FanSuccessfulReachable
open FanSuccessfulChains hiding current original
open FanLambdaChainPassageConsumer

/-- The actual copied-lambda read is at ordinal one, after the body's
FUNCTION read and its real zero-edge lexical variable jump. -/
theorem actual_slot (branch : Bool) :
    (fullEdges branch)[1]?=some (selectedPosition branch).val := by
  cases branch <;> rfl

/-- Direct core use with the real same successful whole chain. The second
candidate is arbitrary at this actual word/finish, not a desired Bool input. -/
theorem actual_candidate_branch_unique
    (principal : SiteActionPrincipal actualFanPresentation.site)
    (source : OccurrenceFragmentSelection current sourceNet (.inl ())) (branch : Bool)
    (candidate : RootAccess targetNet (.inl ()))
    (word : accessWord targetNet candidate.val=selected branch) (candidateBranch : Bool)
    (finish : candidate.val.getLast?=some (targetNet.wire (.inl ⟨.inr (.inl candidateBranch),.inl ()⟩))) :
    candidateBranch=branch := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  have same : SameChainRepresentation source (actualChain branch) (actualChain branch) := rfl
  exact (actualFanPresentation.site.fan_lambda_same_slot_branches
    FanLambdaChainPassageConsumer.actual_source_matches
    (actualFanPresentation.sourceIso.flowBalance flow) rfl principal source
    (actualChain branch) (actualChain branch) same
    (selectedPosition branch) (selectedPosition branch) (actual_slot branch) (actual_slot branch)
    (SuccessfulAuxiliaryPhysicalPair.chosenParent branch) candidate
    (SuccessfulAuxiliaryPhysicalPair.chosenWord branch) word branch candidateBranch
    (SuccessfulAuxiliaryPhysicalPair.chosenFinish branch) finish).symm

/-- The source-Joint wrapper is exercised only under its explicit hypothesis.
This theorem does not claim that source Joint is true for the actual graph. -/
theorem actual_conditional_joint_candidate
    (principal : SiteActionPrincipal actualFanPresentation.site)
    (source : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (joint : JointRepresentation targetClosed source) (branch : Bool)
    (candidate : RootAccess targetNet (.inl ()))
    (word : accessWord targetNet candidate.val=selected branch) (candidateBranch : Bool)
    (finish : candidate.val.getLast?=some (targetNet.wire (.inl ⟨.inr (.inl candidateBranch),.inl ()⟩))) :
    candidateBranch=branch := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  exact (actualFanPresentation.site.fan_lambda_joint_same_slot_branches
    FanLambdaChainPassageConsumer.actual_source_matches
    (actualFanPresentation.sourceIso.flowBalance flow) rfl principal targetClosed source joint
    (actualChain branch) (actualChain branch) ⟨ChainIncidenceIso.refl _⟩
    (selectedPosition branch) (selectedPosition branch) (actual_slot branch) (actual_slot branch)
    (SuccessfulAuxiliaryPhysicalPair.chosenParent branch) candidate
    (SuccessfulAuxiliaryPhysicalPair.chosenWord branch) word branch candidateBranch
    (SuccessfulAuxiliaryPhysicalPair.chosenFinish branch) finish).symm

/-- All data are supplied on one original INIT and real beta/fan-lambda trace.
Both actual Bool branches inhabit a noninitial slot of a genuine 4/5-edge
successful wholechain; no actual source Joint truth is asserted. -/
theorem actual_reachable_slot_synchronization :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet targetNet)
      [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    Matches sourceNet (.inl ()) current.erase ∧Matches targetNet (.inl ()) current.erase ∧
    Closed current.erase ∧
    Nonempty (OccurrenceFragmentSelection current sourceNet (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current targetNet (.inl ())) ∧
    ∃principal : SiteActionPrincipal actualFanPresentation.site,
      ∀ (source : OccurrenceFragmentSelection current sourceNet (.inl ())) (branch : Bool),
      ∃ target : RootAccess targetNet (.inl ()),
        PrerequisiteChain current (starting branch) (fullEdges branch) ∧
        (fullEdges branch).length=(if branch then 5 else 4) ∧
        0<(1:Nat) ∧(fullEdges branch)[1]?=some (selectedPosition branch).val ∧
        (canonicalChainImage source (actualChain branch))[1]?=
          some (source (selectedPosition branch)).fragment.segments ∧
        accessWord targetNet target.val=selected branch ∧
        target.val.getLast?=some (targetNet.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)) ∧
        (∀ (candidate : RootAccess targetNet (.inl ())) (candidateBranch : Bool),
          accessWord targetNet candidate.val=selected branch →
          candidate.val.getLast?=some (targetNet.wire (.inl ⟨.inr (.inl candidateBranch),.inl ()⟩)) →
          candidateBranch=branch) := by
  refine ⟨FanSuccessfulChains.initial,sourceClosed,actualHistory,
    FanLambdaChainPassageConsumer.actual_two_step_trace,
    FanLambdaChainPassageConsumer.actual_source_matches,FanLambdaChainPassageConsumer.actual_target_matches,
    targetClosed,
    FanLambdaChainPassageConsumer.actual_source_matches.occurrence_fragment_selection targetClosed,
    FanLambdaChainPassageConsumer.actual_target_matches.occurrence_fragment_selection targetClosed,?_⟩
  obtain ⟨principal⟩ := actualFanPresentation.site.actionPrincipal_exists
  refine ⟨principal,?_⟩
  intro source branch
  refine ⟨SuccessfulAuxiliaryPhysicalPair.chosenParent branch,actualChain branch,
    (by cases branch <;> rfl),by decide,actual_slot branch,
    canonical_chain_slot source (actualChain branch) (selectedPosition branch) (actual_slot branch),
    SuccessfulAuxiliaryPhysicalPair.chosenWord branch,SuccessfulAuxiliaryPhysicalPair.chosenFinish branch,?_⟩
  intro candidate candidateBranch word finish
  exact actual_candidate_branch_unique principal source branch candidate word candidateBranch finish

#print axioms actual_slot
#print axioms actual_candidate_branch_unique
#print axioms actual_conditional_joint_candidate
#print axioms actual_reachable_slot_synchronization
end Lamping.Checks.FanLambdaSlotSynchronizationConsumer