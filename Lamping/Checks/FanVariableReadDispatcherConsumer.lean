import Lamping.Lamping.FanVariableReadDispatcher
import Lamping.Checks.FanVariableFragmentTransport
namespace Lamping.Checks.FanVariableReadDispatcherConsumer
open AG Graph Lambda Lambda.Labelled FanSuccessfulReachable
open FanSuccessfulChains hiding current original
open FanLambdaChainPassageConsumer FanCurrentVariableBinderConsumer

/-- Four legal choices at the actual function-variable slot invoke BOTH new
complete tops. There is no supplied binding finish, Bool profile or nextslot. -/
theorem actual_complete_pair (principal : SiteActionPrincipal actualFanPresentation.site)
    (sourceFirst sourceSecond : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (targetFirst targetSecond : OccurrenceFragmentSelection current targetNet (.inl ())) (branch : Bool) :
    (sourceFirst (variablePosition branch)).fragment.segments=(sourceSecond (variablePosition branch)).fragment.segments ∧
      (targetFirst (variablePosition branch)).fragment.segments=(targetSecond (variablePosition branch)).fragment.segments := by
  obtain ⟨flow,_,_,transparency,_⟩ := beta_certified
  have forward := actualFanPresentation.site.fan_variable_read_same_slot_forward
    FanLambdaChainPassageConsumer.actual_source_matches FanLambdaChainPassageConsumer.actual_target_matches
    (actualFanPresentation.sourceIso.flowBalance flow) rfl (actualFanPresentation.sourceIso.transparency transparency)
    principal sourceFirst (actualChain branch) (actualChain branch) rfl
    (variablePosition branch) (variablePosition branch) (actual_function_slots branch).2.1 (actual_function_slots branch).2.1
    (variable_lookup branch) (variable_lookup branch)
    (targetFirst (variablePosition branch)) (targetSecond (variablePosition branch))
  have reflection := actualFanPresentation.site.fan_variable_read_same_slot_reflect
    FanLambdaChainPassageConsumer.actual_source_matches FanLambdaChainPassageConsumer.actual_target_matches
    (actualFanPresentation.sourceIso.flowBalance flow) rfl principal targetFirst (actualChain branch) (actualChain branch) rfl
    (variablePosition branch) (variablePosition branch) (actual_function_slots branch).2.1 (actual_function_slots branch).2.1
    (variable_lookup branch) (variable_lookup branch)
    (sourceFirst (variablePosition branch)) (sourceSecond (variablePosition branch))
  exact ⟨reflection,forward⟩

/-- Genuine SAME INIT/history two-rule fixture. Four/five-edge chains read
CURRENT variable FUNCTION at0 then lexical lambda at1, not an ordinary bindctx
turn. Each branch uses samechain reflexive REP, not cross-chain Joint truth. -/
theorem actual_reachable_complete_supply :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧Closed current.erase ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet targetNet)
      [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    Matches sourceNet (.inl ()) current.erase ∧Matches targetNet (.inl ()) current.erase ∧
    Transparency sourceNet (.inl ()) ∧
    Nonempty (OccurrenceFragmentSelection current sourceNet (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current targetNet (.inl ())) ∧
    ∃principal : SiteActionPrincipal actualFanPresentation.site,
      ∀ (sourceFirst sourceSecond : OccurrenceFragmentSelection current sourceNet (.inl ()))
        (targetFirst targetSecond : OccurrenceFragmentSelection current targetNet (.inl ())) (branch : Bool),
        PrerequisiteChain current (starting branch) (fullEdges branch) ∧
        (fullEdges branch).length=(if branch then 5 else 4) ∧
        (fullEdges branch)[0]?=some (variablePath branch) ∧
        (fullEdges branch)[1]?=some (selected branch) ∧
        (sourceFirst (variablePosition branch)).fragment.segments=(sourceSecond (variablePosition branch)).fragment.segments ∧
        (targetFirst (variablePosition branch)).fragment.segments=(targetSecond (variablePosition branch)).fragment.segments := by
  obtain ⟨_flow,_balance,_inputs,transparency,_matching⟩ := beta_certified
  refine ⟨FanSuccessfulChains.initial,sourceClosed,actualHistory,targetClosed,
    FanLambdaChainPassageConsumer.actual_two_step_trace,
    FanLambdaChainPassageConsumer.actual_source_matches,FanLambdaChainPassageConsumer.actual_target_matches,
    actualFanPresentation.sourceIso.transparency transparency,
    FanLambdaChainPassageConsumer.actual_source_matches.occurrence_fragment_selection targetClosed,
    FanLambdaChainPassageConsumer.actual_target_matches.occurrence_fragment_selection targetClosed,?_⟩
  obtain ⟨principal⟩ := actualFanPresentation.site.actionPrincipal_exists
  refine ⟨principal,?_⟩
  intro sourceFirst sourceSecond targetFirst targetSecond branch
  have compared := actual_complete_pair principal sourceFirst sourceSecond targetFirst targetSecond branch
  exact ⟨actualChain branch,(by cases branch <;> rfl),(actual_function_slots branch).2.1,
    (actual_function_slots branch).2.2.1,compared.1,compared.2⟩
end Lamping.Checks.FanVariableReadDispatcherConsumer
#print axioms Lamping.AG.Matches.variable_access_typed
#print axioms Lamping.AG.PathSite.fan_variable_access_cases
#print axioms Lamping.AG.SourceEdgeFragment.fan_kept_parent_copied_binding_reflect
#print axioms Lamping.AG.SourceEdgeFragment.fan_lambda_copied_binding_vs_kept_terminal
#print axioms Lamping.AG.PathSite.fan_variable_read_same_slot_forward
#print axioms Lamping.AG.PathSite.fan_variable_read_same_slot_reflect
#print axioms Lamping.Checks.FanVariableReadDispatcherConsumer.actual_complete_pair
#print axioms Lamping.Checks.FanVariableReadDispatcherConsumer.actual_reachable_complete_supply
