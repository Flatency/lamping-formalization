import Lamping.Lamping.FanCurrentVariableBinders
import Lamping.Checks.FanLambdaChainPassages
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanCurrentVariableBinderConsumer
open AG Graph Lambda Lambda.Labelled FanSuccessfulReachable
open FanSuccessfulChains hiding current original
open FanLambdaChainPassageConsumer
abbrev variablePath (branch : Bool) : Path := if branch then rightVar else leftVar
def variablePosition (branch : Bool) : Position current.erase := ⟨variablePath branch,by cases branch <;> rfl⟩

theorem variable_lookup (branch : Bool) : current.subterm (variablePath branch)=some (.var (.atom 11) 0) := by
  cases branch <;> rfl

theorem binder_lookup (branch : Bool) : current.subterm (selected branch)=
    some (.lam (if branch then rightLabel else leftLabel) callerBody) := by
  cases branch <;> rfl

theorem lexical_split (branch : Bool) : variablePath branch=selected branch++[.body,.fn] := by
  cases branch <;> rfl

/-- Actual matched lexical decomposition plus the independently supplied
real lambda context path derives the variable's copied binding finish. -/
theorem actual_variable_finish (branch : Bool)
    (leaf : RootAccess targetNet (.inl ())) (word : accessWord targetNet leaf.val=variablePath branch) :
    leaf.val.getLast?=some (targetNet.wire (.inl ⟨.inr (.inl branch),lamBind⟩)) := by
  obtain ⟨loop,a,b,c,binding,ctx,split,_loopWord,_ctxRole,parentFinish,_labels⟩ :=
    FanLambdaChainPassageConsumer.actual_target_matches.current_lexical_binding_access
      (variable_lookup branch) (lexical_split branch) rfl leaf
      (SuccessfulAuxiliaryPhysicalPair.chosenParent branch) word
      (SuccessfulAuxiliaryPhysicalPair.chosenWord branch)
  have wires := Option.some.inj (parentFinish.symm.trans (SuccessfulAuxiliaryPhysicalPair.chosenFinish branch))
  have ends := congrArg targetNet.wire.mate wires
  simp only [Pairing.involutive] at ends
  have sameNode : binding.binder=.inr (.inl branch) := congrArg Sigma.fst (Sum.inl.inj ends)
  have sameBind : (.inl ⟨binding.binder,binding.bind⟩ : Endpoint targetNet)=.inl ⟨.inr (.inl branch),lamBind⟩ :=
    congrArg Sum.inl (Sigma.ext sameNode binding.bind_role)
  rw [split,List.getLast?_append,binding.finish,sameBind]
  rfl

/-- The variable is THIS actual body FUNCTION read at slot zero, and the
same copied lambda's incoming edge is the next read at slot one. -/
theorem actual_function_slots (branch : Bool) :
    fullEdges branch=variablePath branch::remainingEdges branch ∧
    (fullEdges branch)[0]?=some (variablePath branch) ∧
    (fullEdges branch)[1]?=some (selected branch) ∧
    current.subterm (starting branch)=some (.app (.atom 10) (.var (.atom 11) 0) (.lam (.atom 12) (.var (.atom 13) 0))) ∧
    variablePath branch=starting branch++[.fn] := by
  cases branch <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem actual_current_binder_jump (branch : Bool)
    (leaf : RootAccess targetNet (.inl ())) (word : accessWord targetNet leaf.val=variablePath branch)
    {a b : Context} (whole : Labelling targetNet leaf.val a b) :
    ∃ (loop : List (Endpoint targetNet)) (seam : Context) (binding : BindingLoop targetNet loop seam b),
      leaf.val=(SuccessfulAuxiliaryPhysicalPair.chosenParent branch).val++loop ∧
      binding.binder=.inr (.inl branch) ∧accessWord targetNet loop=[.fn] ∧
      (SuccessfulAuxiliaryPhysicalPair.chosenParent branch).val.getLast?=
        some (targetNet.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)) ∧
      Labelling targetNet (SuccessfulAuxiliaryPhysicalPair.chosenParent branch).val a seam ∧
      PrerequisitePrefix current (variablePath branch) [] (selected branch) ∧
      PrerequisiteChain current (variablePath branch) (remainingEdges branch) ∧
      (remainingEdges branch).head?=some (selected branch) ∧
      PrerequisiteReads current (selected branch) (selected branch) := by
  obtain ⟨flow,_,_,transparency,_⟩ := beta_certified
  exact actualFanPresentation.site.fan_current_variable_binder
    FanLambdaChainPassageConsumer.actual_target_matches
    (actualFanPresentation.sourceIso.flowBalance flow) rfl
    (actualFanPresentation.sourceIso.transparency transparency)
    (variable_lookup branch) (binder_lookup branch) (lexical_split branch) rfl
    leaf (SuccessfulAuxiliaryPhysicalPair.chosenParent branch) word
    (SuccessfulAuxiliaryPhysicalPair.chosenWord branch) branch (actual_variable_finish branch leaf word)
    whole (actualRemainder branch)

/-- SAME original INIT/history, actual two-rule trace and actual fragment
supply make both current FUNCTION-variable/zero-jump/context transitions real.
The same whole assignment is retained; no Joint or branch profile is assumed. -/
theorem actual_reachable_current_binders :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet targetNet)
      [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    Matches sourceNet (.inl ()) current.erase ∧Matches targetNet (.inl ()) current.erase ∧
    Closed current.erase ∧
    Nonempty (OccurrenceFragmentSelection current targetNet (.inl ())) ∧
    (∀branch,PrerequisiteChain current (starting branch) (fullEdges branch) ∧
      fullEdges branch=variablePath branch::remainingEdges branch ∧
      (fullEdges branch)[0]?=some (variablePath branch) ∧
      (fullEdges branch)[1]?=some (selected branch)) ∧
    ∀ (selection : OccurrenceFragmentSelection current targetNet (.inl ())) (branch : Bool),
      ∃ (a b : Context) (loop : List (Endpoint targetNet)) (seam : Context)
        (binding : BindingLoop targetNet loop seam b),
        Labelling targetNet (selection (variablePosition branch)).fragment.access.val a b ∧
        (selection (variablePosition branch)).fragment.access.val=
          (SuccessfulAuxiliaryPhysicalPair.chosenParent branch).val++loop ∧
        binding.binder=.inr (.inl branch) ∧accessWord targetNet loop=[.fn] ∧
        (SuccessfulAuxiliaryPhysicalPair.chosenParent branch).val.getLast?=
          some (targetNet.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)) ∧
        Labelling targetNet (SuccessfulAuxiliaryPhysicalPair.chosenParent branch).val a seam ∧
        PrerequisitePrefix current (variablePath branch) [] (selected branch) ∧
        PrerequisiteChain current (variablePath branch) (remainingEdges branch) ∧
        (remainingEdges branch).head?=some (selected branch) ∧
        PrerequisiteReads current (selected branch) (selected branch) := by
  refine ⟨FanSuccessfulChains.initial,sourceClosed,actualHistory,
    FanLambdaChainPassageConsumer.actual_two_step_trace,
    FanLambdaChainPassageConsumer.actual_source_matches,FanLambdaChainPassageConsumer.actual_target_matches,
    targetClosed,FanLambdaChainPassageConsumer.actual_target_matches.occurrence_fragment_selection targetClosed,?_,?_⟩
  · intro branch
    have slots := actual_function_slots branch
    exact ⟨actualChain branch,slots.1,slots.2.1,slots.2.2.1⟩
  · intro selection branch
    let leaf := (selection (variablePosition branch)).fragment.access
    obtain ⟨a,b,whole⟩ := leaf.property.1.1
    obtain ⟨loop,seam,binding,split,binderEq,loopWord,finish,labels,jump,next,head,reads⟩ :=
      actual_current_binder_jump branch leaf (selection (variablePosition branch)).fragment.word whole
    exact ⟨a,b,loop,seam,binding,whole,split,binderEq,loopWord,finish,labels,jump,next,head,reads⟩

#print axioms variable_lookup
#print axioms lexical_split
#print axioms actual_variable_finish
#print axioms actual_function_slots
#print axioms actual_current_binder_jump
#print axioms actual_reachable_current_binders
end Lamping.Checks.FanCurrentVariableBinderConsumer