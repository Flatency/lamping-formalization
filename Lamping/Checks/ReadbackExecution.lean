import Lamping.Lamping.ReadbackMachineExecution
import Lamping.Lamping.ExecutableEncoding
import Lamping.Lamping.InitialPathControls

namespace Lamping.Checks.ReadbackExecution
open AG Graph Lambda AG.Readback
private abbrev net := (encode 0 (.lam (.var 0))).net
private abbrev root : Endpoint net := .inr (.inl (.inl ()))
private abbrev body : Endpoint net := .inl ⟨.inl (),lamBody⟩
private def frame : BinderFrame net := ⟨.inl (),0,[root],body,[]⟩
private def start : MachineState net := ⟨[.read body [] [root] [frame]],[]⟩

/-- The real four-segment binding access induces exactly three scanner
machine transitions. The last two transitions read the variable and finish. -/
theorem actual_binding_execution :
    ∃ state,MachineSteps net 3 start state ∧
      machineFuel net 3 start=.exhausted state ∧machineFuel net 2 state=.done (.var 0) := by
  let loop := identityBindingLoop 0 Context.empty Context.empty
  obtain ⟨data,last,trace,_output,literal⟩ := scanSteps_of_control_path net loop.proper
    (loop.forward.empty_word_control_only rfl) body rfl [] (by simp)
  have steps := trace.machineSteps [root] [frame] [] []
  change MachineSteps net 3 start _ at steps
  refine ⟨_,steps,steps.fuel_exhausted,?_⟩
  rw [←steps.fuel_more 2]
  rfl

/-- Resuming fuel preserves the actual intermediate state instead of
restarting the scan or choosing another access path. -/
theorem actual_execution_resume :
    ∃ state,MachineSteps net 3 start state ∧machineFuel net (3+2) start=machineFuel net 2 state := by
  obtain ⟨state,steps,_first,_last⟩ := actual_binding_execution
  exact ⟨state,steps,steps.fuel_more 2⟩

#print axioms MachineSteps.append
#print axioms MachineSteps.fuel_more
#print axioms ScanSteps.machineSteps
#print axioms scanSteps_of_control_path
#print axioms actual_binding_execution
end Lamping.Checks.ReadbackExecution
