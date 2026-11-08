import Lamping.Lamping.FanVariableFragmentTransport
import Lamping.Checks.FanCurrentVariableBinders
namespace Lamping.Checks.FanVariableFragmentConsumer
open AG Graph Lambda Lambda.Labelled FanSuccessfulReachable
open FanSuccessfulChains hiding current original
open FanLambdaChainPassageConsumer FanCurrentVariableBinderConsumer
/-- Direct successful-slot use. Target choices are arbitrary lawful fragments;
no target-piece equality or normalized-piece certificate is supplied. -/
theorem actual_successful_variable_forward
    (principal : SiteActionPrincipal actualFanPresentation.site)
    (source : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (firstTarget secondTarget : OccurrenceFragmentSelection current targetNet (.inl ())) (branch : Bool) :
    (firstTarget (variablePosition branch)).fragment.segments=
      (secondTarget (variablePosition branch)).fragment.segments := by
  obtain ⟨flow,_,_,transparency,_⟩ := beta_certified
  exact actualFanPresentation.site.fan_variable_same_slot_fragment_forward
    FanLambdaChainPassageConsumer.actual_source_matches FanLambdaChainPassageConsumer.actual_target_matches
    (actualFanPresentation.sourceIso.flowBalance flow) rfl
    (actualFanPresentation.sourceIso.transparency transparency) principal source
    (actualChain branch) (actualChain branch) rfl (variablePosition branch) (variablePosition branch)
    (actual_function_slots branch).2.1 (actual_function_slots branch).2.1
    (variable_lookup branch) (variable_lookup branch)
    (firstTarget (variablePosition branch)) (secondTarget (variablePosition branch)) branch branch
    (actual_variable_finish branch _ (firstTarget (variablePosition branch)).fragment.word)
    (actual_variable_finish branch _ (secondTarget (variablePosition branch)).fragment.word)

/-- The same actual geometry also consumes the explicit conditional Joint
wrapper; source Joint truth is not asserted for this fixture. -/
theorem actual_conditional_joint_forward
    (principal : SiteActionPrincipal actualFanPresentation.site)
    (source : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (joint : JointRepresentation targetClosed source)
    (firstTarget secondTarget : OccurrenceFragmentSelection current targetNet (.inl ())) (branch : Bool) :
    (firstTarget (variablePosition branch)).fragment.segments=
      (secondTarget (variablePosition branch)).fragment.segments := by
  obtain ⟨flow,_,_,transparency,_⟩ := beta_certified
  exact actualFanPresentation.site.fan_variable_joint_same_slot_fragment_forward
    FanLambdaChainPassageConsumer.actual_source_matches FanLambdaChainPassageConsumer.actual_target_matches
    (actualFanPresentation.sourceIso.flowBalance flow) rfl
    (actualFanPresentation.sourceIso.transparency transparency) principal targetClosed source joint
    (actualChain branch) (actualChain branch) ⟨ChainIncidenceIso.refl _⟩
    (variablePosition branch) (variablePosition branch)
    (actual_function_slots branch).2.1 (actual_function_slots branch).2.1
    (variable_lookup branch) (variable_lookup branch)
    (firstTarget (variablePosition branch)) (secondTarget (variablePosition branch)) branch branch
    (actual_variable_finish branch _ (firstTarget (variablePosition branch)).fragment.word)
    (actual_variable_finish branch _ (secondTarget (variablePosition branch)).fragment.word)

/-- SAME original INIT/history and genuine two-rule trace. All four legal
source/target choices exist. The physical core is tested on the real same
4/5-edge successful chain, not on the all-NoChain BODY regression. -/
theorem actual_reachable_variable_fragment_transport :
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
        (fullEdges branch)[0]?=some (variablePath branch) ∧
        (fullEdges branch)[1]?=some (selected branch) ∧
        (firstSource (variablePosition branch)).fragment.segments=
          (secondSource (variablePosition branch)).fragment.segments ∧
        (firstTarget (variablePosition branch)).fragment.segments=
          (secondTarget (variablePosition branch)).fragment.segments := by
  refine ⟨FanSuccessfulChains.initial,sourceClosed,actualHistory,
    FanLambdaChainPassageConsumer.actual_two_step_trace,
    FanLambdaChainPassageConsumer.actual_source_matches,FanLambdaChainPassageConsumer.actual_target_matches,
    targetClosed,
    FanLambdaChainPassageConsumer.actual_source_matches.occurrence_fragment_selection targetClosed,
    FanLambdaChainPassageConsumer.actual_target_matches.occurrence_fragment_selection targetClosed,?_⟩
  obtain ⟨principal⟩ := actualFanPresentation.site.actionPrincipal_exists
  refine ⟨principal,?_⟩
  intro firstSource secondSource firstTarget secondTarget branch
  exact ⟨actualChain branch,(by cases branch <;> rfl),(actual_function_slots branch).2.1,
    (actual_function_slots branch).2.2.1,
    OccurrenceFragment.segments_unique FanLambdaChainPassageConsumer.actual_source_matches _ _,
    actual_successful_variable_forward principal firstSource firstTarget secondTarget branch⟩
#print axioms PendingRhsBlock.fan_aux_canonical_trim
#print axioms PathSite.fan_aux_canonical_access
#print axioms SourceEdgeFragment.fan_kept_parent_copied_binding_cut
#print axioms SourceEdgeFragment.fan_kept_parent_copied_binding_forward
#print axioms OccurrenceFragment.variable_function_parent
#print axioms PathSite.fan_variable_same_slot_fragment_forward
#print axioms PathSite.fan_variable_joint_same_slot_fragment_forward
#print axioms actual_successful_variable_forward
#print axioms actual_conditional_joint_forward
#print axioms actual_reachable_variable_fragment_transport
end Lamping.Checks.FanVariableFragmentConsumer
