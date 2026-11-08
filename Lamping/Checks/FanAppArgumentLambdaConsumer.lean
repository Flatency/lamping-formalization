import Lamping.Lamping.FanAppArgumentLambdaTransport
import Lamping.Checks.FanAppFunctionVariableConsumer
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanAppArgumentLambdaConsumer
open AG Graph Lambda Lambda.Labelled FanSuccessfulReachable FanAppSuccessfulReachable
open FanSuccessfulChains hiding current original
open FanLambdaChainPassageConsumer FanCurrentVariableBinderConsumer
open FanAppFunctionVariableConsumer
abbrev argumentPath (branch : Bool) : Path := starting branch++[.arg]
def argumentPosition (branch : Bool) : Position current.erase := ⟨argumentPath branch,by cases branch <;> rfl⟩
abbrev argumentEdges (branch : Bool) : List Path := argumentPath branch::fullEdges branch

theorem argument_lookup (branch : Bool) : current.subterm (argumentPath branch)=some (.lam (.atom 12) (.var (.atom 13) 0)) := by
  cases branch <;> rfl

def argumentChain (branch : Bool) : PrerequisiteChain current (argumentPath branch) (argumentEdges branch) :=
  .lam (parent:=starting branch) (step:=.arg) (argument_lookup branch) (by decide) (actualChain branch)

theorem argument_slots (branch : Bool) :
    (argumentEdges branch).length=(if branch then 6 else 5) ∧
    (argumentEdges branch)[0]?=some (argumentPath branch) ∧
    (argumentEdges branch)[1]?=some (variablePath branch) := by
  cases branch <;> exact ⟨rfl,rfl,rfl⟩

theorem actual_argument_incoming
    {N W : Type} [FiniteNames N] [FiniteNames W] {g : Net signature N (Boundary term) W}
    (selection : OccurrenceFragmentSelection current g (.inl ())) (branch : Bool) :
    ∃stamp,(selection (argumentPosition branch)).context=.appArg stamp := by
  have bodyLookup : current.subterm (starting branch)=some callerBody := by cases branch <;> rfl
  obtain ⟨env,ctx,parentOccurrence⟩ := SourceSubterm.of_lookup current bodyLookup [] .external
  have child : SourceSubterm [] .external current (argumentPath branch) env (.appArg (.atom 10)) (.lam (.atom 12) (.var (.atom 13) 0)) :=
    parentOccurrence.append (.arg .nil)
  exact ⟨_,((selection (argumentPosition branch)).occurrence.same_occurrence child).2.1⟩

theorem actual_next_function
    (source : OccurrenceFragmentSelection current fanApp.site.net (.inl ())) (branch : Bool) :
    ∃parent appStamp fn more,argumentPath branch=parent++[.arg] ∧
      current.subterm parent=some (.app appStamp fn (.lam (.atom 12) (.var (.atom 13) 0))) ∧
      PrerequisiteChain current parent more ∧
      (argumentEdges branch)[1]?=some (parent++[.fn]) ∧
      PrerequisitePrefix current (argumentPath branch) [argumentPath branch] parent :=
  (argumentChain branch).argument_lambda_next_function_slot (argument_slots branch).2.1 (argument_lookup branch)
    (source (argumentPosition branch)).occurrence (actual_argument_incoming source branch)

/-- Typed lambda endpoints are actually kept by this fanAPP rule. -/
theorem actual_lambda_terminal_kept
    (target : OccurrenceFragmentSelection current fanApp.site.reduce (.inl ())) (branch : Bool) :
    ∃ port : NodePort signature fanApp.Kept fanApp.kept,
      (target (argumentPosition branch)).fragment.access.val.getLast?=
        some (fanApp.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  have excluded : ∀port : Port (.op .app),portKind (.op .app) port≠some AccessKind.lam := by
    intro port wrong
    rcases port with u|aux
    · cases u;cases wrong
    · cases aux <;> cases wrong
  have typed := FanAppSuccessfulReachable.actual_target_matches.lambda_access_typed
    (argument_lookup branch) (target (argumentPosition branch)).fragment.access (target (argumentPosition branch)).fragment.word
  exact fanApp.site.action_access_kept_of_kind_excluded (.fan .app 0 1 (by decide))
    (target (argumentPosition branch)).fragment.access typed excluded

/-- The complete natural top derives nextslot/Bool/parents internally. -/
theorem actual_successful_argument_forward
    (principal : SiteActionPrincipal fanApp.site)
    (source : OccurrenceFragmentSelection current fanApp.site.net (.inl ()))
    (firstTarget secondTarget : OccurrenceFragmentSelection current fanApp.site.reduce (.inl ())) (branch : Bool) :
    (firstTarget (argumentPosition branch)).fragment.segments=(secondTarget (argumentPosition branch)).fragment.segments := by
  obtain ⟨flow,_,inputs,_,_⟩ := cro_certified
  exact fanApp.site.fan_app_argument_lambda_same_slot_forward FanAppSuccessfulReachable.actual_source_matches
    FanAppSuccessfulReachable.actual_target_matches (fanApp.sourceIso.rootInputs inputs) (fanApp.sourceIso.flowBalance flow) rfl
    principal source (argumentChain branch) (argumentChain branch) rfl
    (argumentPosition branch) (argumentPosition branch) (argument_slots branch).2.1 (argument_slots branch).2.1
    (argument_lookup branch) (argument_lookup branch) (actual_argument_incoming source branch) (actual_argument_incoming source branch)
    (firstTarget (argumentPosition branch)) (secondTarget (argumentPosition branch))

theorem actual_reachable_argument_lambda_transport :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet fanApp.site.reduce)
      [.beta 0,.fanAction .lam 0 1 (by decide),.fanAction .cro 0 1 (by decide),.fanAction .app 0 1 (by decide)] ∧
    Matches fanApp.site.net (.inl ()) current.erase ∧Matches fanApp.site.reduce (.inl ()) current.erase ∧
    Nonempty (OccurrenceFragmentSelection current fanApp.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current fanApp.site.reduce (.inl ())) ∧
    ∃ principal : SiteActionPrincipal fanApp.site,
      ∀ (firstSource secondSource : OccurrenceFragmentSelection current fanApp.site.net (.inl ()))
        (firstTarget secondTarget : OccurrenceFragmentSelection current fanApp.site.reduce (.inl ())) (branch : Bool),
      PrerequisiteChain current (argumentPath branch) (argumentEdges branch) ∧
      (argumentEdges branch).length=(if branch then 6 else 5) ∧
      (argumentEdges branch)[0]?=some (argumentPath branch) ∧
      (argumentEdges branch)[1]?=some (variablePath branch) ∧
      (firstSource (argumentPosition branch)).fragment.segments=(secondSource (argumentPosition branch)).fragment.segments ∧
      (firstTarget (argumentPosition branch)).fragment.segments=(secondTarget (argumentPosition branch)).fragment.segments ∧
      (∃ copy,(targetAppParent branch).val.getLast?=some (fanApp.site.reduce.wire (.inl ⟨.inr (.inl copy),appCtx⟩))) ∧
      (∃ port : NodePort signature fanApp.Kept fanApp.kept,
        (firstTarget (argumentPosition branch)).fragment.access.val.getLast?=
          some (fanApp.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩))) := by
  refine ⟨FanSuccessfulChains.initial,sourceClosed,actualHistory,FanAppSuccessfulReachable.actual_four_step_trace,
    FanAppSuccessfulReachable.actual_source_matches,FanAppSuccessfulReachable.actual_target_matches,
    FanAppSuccessfulReachable.actual_source_matches.occurrence_fragment_selection targetClosed,
    FanAppSuccessfulReachable.actual_target_matches.occurrence_fragment_selection targetClosed,?_⟩
  obtain ⟨principal⟩ := fanApp.site.actionPrincipal_exists
  refine ⟨principal,?_⟩
  intro firstSource secondSource firstTarget secondTarget branch
  exact ⟨argumentChain branch,(argument_slots branch).1,(argument_slots branch).2.1,(argument_slots branch).2.2,
    OccurrenceFragment.segments_unique FanAppSuccessfulReachable.actual_source_matches _ _,
    actual_successful_argument_forward principal firstSource firstTarget secondTarget branch,
    targetAppCopied branch,actual_lambda_terminal_kept firstTarget branch⟩
end Lamping.Checks.FanAppArgumentLambdaConsumer
#print axioms Lamping.AG.fan_app_typed_argument_prefix
#print axioms Lamping.AG.fan_app_copied_argument_fragment
#print axioms Lamping.AG.PendingRhsBlock.fan_app_argument_padding
#print axioms Lamping.AG.PathSite.fan_app_argument_padding_access
#print axioms Lamping.AG.SourceEdgeFragment.fan_app_copied_argument_kept_cut
#print axioms Lamping.Lambda.Labelled.PrerequisiteChain.argument_lambda_next_function_slot
#print axioms Lamping.AG.SourceEdgeFragment.fan_app_copied_argument_kept_forward
#print axioms Lamping.AG.PathSite.fan_app_argument_lambda_same_slot_forward
#print axioms Lamping.Checks.FanAppArgumentLambdaConsumer.argumentChain
#print axioms Lamping.Checks.FanAppArgumentLambdaConsumer.argument_slots
#print axioms Lamping.Checks.FanAppArgumentLambdaConsumer.actual_argument_incoming
#print axioms Lamping.Checks.FanAppArgumentLambdaConsumer.actual_next_function
#print axioms Lamping.Checks.FanAppArgumentLambdaConsumer.actual_lambda_terminal_kept
#print axioms Lamping.Checks.FanAppArgumentLambdaConsumer.actual_successful_argument_forward
#print axioms Lamping.Checks.FanAppArgumentLambdaConsumer.actual_reachable_argument_lambda_transport
