import Lamping.Lamping.FanVariableSlotSynchronization
import Lamping.Checks.FanCurrentVariableBinders
namespace Lamping.Checks.FanVariableSlotConsumer
open AG Graph Lambda Lambda.Labelled FanSuccessfulReachable
open FanSuccessfulChains hiding current original
open FanLambdaChainPassageConsumer FanCurrentVariableBinderConsumer
/-- The next ordinal is derived from the chain, not supplied as a premise.
The lexical split uniquely identifies the actual CURRENT selected lambda. -/
theorem actual_next_binder_slot (branch : Bool) :
    ∃ origin body more,
      current.subterm (selected branch)=some (.lam origin body) ∧
      PrerequisiteChain current (selected branch) more ∧
      (fullEdges branch)[0+1]?=some (selected branch) ∧
      PrerequisitePrefix current (variablePath branch) [] (selected branch) := by
  obtain ⟨parent,rest,origin,body,more,lexical,depth,lookup,next,slot,jump⟩ :=
    (actualChain branch).variable_next_slot (actual_function_slots branch).2.1 (variable_lookup branch)
  have same := binding_prefix_depth_unique (lexical.symm.trans (lexical_split branch))
    (by simpa only [binderDepth] using depth.symm)
  rw [same.1] at lookup next slot jump
  exact ⟨origin,body,more,lookup,next,slot,jump⟩

/-- Both real slot-zero variable reads are supplied, while the next copied
lambda slot and its Bool are recovered internally by the new core. -/
theorem actual_candidate_binding_branch_unique
    (principal : SiteActionPrincipal actualFanPresentation.site)
    (source : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (target : OccurrenceFragmentSelection current targetNet (.inl ())) (branch : Bool)
    (candidate : RootAccess targetNet (.inl ()))
    (word : accessWord targetNet candidate.val=variablePath branch) (candidateBranch : Bool)
    (finish : candidate.val.getLast?=some (targetNet.wire (.inl ⟨.inr (.inl candidateBranch),lamBind⟩))) :
    candidateBranch=branch := by
  obtain ⟨flow,_,_,transparency,_⟩ := beta_certified
  let reference := (target (variablePosition branch)).fragment.access
  have referenceWord := (target (variablePosition branch)).fragment.word
  exact (actualFanPresentation.site.fan_variable_same_slot_branches
    FanLambdaChainPassageConsumer.actual_source_matches FanLambdaChainPassageConsumer.actual_target_matches
    (actualFanPresentation.sourceIso.flowBalance flow) rfl
    (actualFanPresentation.sourceIso.transparency transparency) principal source
    (actualChain branch) (actualChain branch) rfl (variablePosition branch) (variablePosition branch)
    (actual_function_slots branch).2.1 (actual_function_slots branch).2.1
    (variable_lookup branch) (variable_lookup branch) reference candidate referenceWord word
    branch candidateBranch (actual_variable_finish branch reference referenceWord) finish).symm

/-- Only a conditional use of the genuine source Joint wrapper. -/
theorem actual_conditional_joint_candidate
    (principal : SiteActionPrincipal actualFanPresentation.site)
    (source : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (joint : JointRepresentation targetClosed source)
    (target : OccurrenceFragmentSelection current targetNet (.inl ())) (branch : Bool)
    (candidate : RootAccess targetNet (.inl ()))
    (word : accessWord targetNet candidate.val=variablePath branch) (candidateBranch : Bool)
    (finish : candidate.val.getLast?=some (targetNet.wire (.inl ⟨.inr (.inl candidateBranch),lamBind⟩))) :
    candidateBranch=branch := by
  obtain ⟨flow,_,_,transparency,_⟩ := beta_certified
  let reference := (target (variablePosition branch)).fragment.access
  have referenceWord := (target (variablePosition branch)).fragment.word
  exact (actualFanPresentation.site.fan_variable_joint_same_slot_branches
    FanLambdaChainPassageConsumer.actual_source_matches FanLambdaChainPassageConsumer.actual_target_matches
    (actualFanPresentation.sourceIso.flowBalance flow) rfl
    (actualFanPresentation.sourceIso.transparency transparency) principal targetClosed source joint
    (actualChain branch) (actualChain branch) ⟨ChainIncidenceIso.refl _⟩
    (variablePosition branch) (variablePosition branch)
    (actual_function_slots branch).2.1 (actual_function_slots branch).2.1
    (variable_lookup branch) (variable_lookup branch) reference candidate referenceWord word
    branch candidateBranch (actual_variable_finish branch reference referenceWord) finish).symm

/-- One actual original INIT/history and two GraphSteps supply both 4/5-edge
successful chains, all selections and the real slot0-variable/slot1-lambda
transitions. This is a samechain core test, not actual source Joint truth. -/
theorem actual_reachable_variable_slot_synchronization :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet targetNet)
      [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    Matches sourceNet (.inl ()) current.erase ∧Matches targetNet (.inl ()) current.erase ∧
    Closed current.erase ∧
    Nonempty (OccurrenceFragmentSelection current sourceNet (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current targetNet (.inl ())) ∧
    ∃ principal : SiteActionPrincipal actualFanPresentation.site,
      ∀ (source : OccurrenceFragmentSelection current sourceNet (.inl ()))
        (target : OccurrenceFragmentSelection current targetNet (.inl ())) (branch : Bool),
        PrerequisiteChain current (starting branch) (fullEdges branch) ∧
        (fullEdges branch).length=(if branch then 5 else 4) ∧
        (fullEdges branch)[0]?=some (variablePath branch) ∧
        (∃ origin body more,
          current.subterm (selected branch)=some (.lam origin body) ∧
          PrerequisiteChain current (selected branch) more ∧
          (fullEdges branch)[0+1]?=some (selected branch) ∧
          PrerequisitePrefix current (variablePath branch) [] (selected branch)) ∧
        (∀ (candidate : RootAccess targetNet (.inl ())) (candidateBranch : Bool),
          accessWord targetNet candidate.val=variablePath branch →
          candidate.val.getLast?=some (targetNet.wire (.inl ⟨.inr (.inl candidateBranch),lamBind⟩)) →
          candidateBranch=branch) := by
  refine ⟨FanSuccessfulChains.initial,sourceClosed,actualHistory,
    FanLambdaChainPassageConsumer.actual_two_step_trace,
    FanLambdaChainPassageConsumer.actual_source_matches,FanLambdaChainPassageConsumer.actual_target_matches,
    targetClosed,
    FanLambdaChainPassageConsumer.actual_source_matches.occurrence_fragment_selection targetClosed,
    FanLambdaChainPassageConsumer.actual_target_matches.occurrence_fragment_selection targetClosed,?_⟩
  obtain ⟨principal⟩ := actualFanPresentation.site.actionPrincipal_exists
  refine ⟨principal,?_⟩
  intro source target branch
  exact ⟨actualChain branch,(by cases branch <;> rfl),(actual_function_slots branch).2.1,
    actual_next_binder_slot branch,fun candidate candidateBranch word finish=>
      actual_candidate_binding_branch_unique principal source target branch candidate word candidateBranch finish⟩
#print axioms actual_next_binder_slot
#print axioms actual_candidate_binding_branch_unique
#print axioms actual_conditional_joint_candidate
#print axioms actual_reachable_variable_slot_synchronization
end Lamping.Checks.FanVariableSlotConsumer
