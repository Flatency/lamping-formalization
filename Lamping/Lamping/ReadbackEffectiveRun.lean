import Lamping.Lamping.ReadbackMachineExecution

namespace Lamping.AG.Readback
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable [DecidableEq N] [DecidableEq B] [DecidableEq W]
variable (g : Net signature N B W)

def MachineNext (after before : MachineState g) : Prop := machineStep g before=.next after

/-- A finite successful fuel run proves accessibility of the actual next
relation. Only a proposition is built; no fuel or output is chosen as data. -/
theorem accessible_of_fuel {fuel : Nat} {state : MachineState g} {term : Term}
    (run : machineFuel g fuel state=.done term) : Acc (MachineNext g) state := by
  induction fuel generalizing state with
  | zero => cases run
  | succ fuel ih =>
    apply Acc.intro
    intro next step
    change machineStep g state=.next next at step
    exact ih (by simpa only [machineFuel,step] using run)

/-- States with a proof of accessibility, erased by the evaluator. -/
def AccessibleState := {state : MachineState g // Acc (MachineNext g) state}

instance : WellFoundedRelation (AccessibleState g) where
  rel := InvImage (MachineNext g) Subtype.val
  wf := ⟨fun state => InvImage.accessible Subtype.val state.property⟩

/-- Execution follows actual machine steps; the domain proof supplies only
well-foundedness and is erased by compilation. -/
def runOnAccessible (state : AccessibleState g) : Option Term :=
  match actual : machineStep g state.val with
  | .next next => runOnAccessible ⟨next,state.property.inv actual⟩
  | .done term => some term
  | .failed _ => none
termination_by state
decreasing_by exact actual

def runAccessible (state : MachineState g) (accessible : Acc (MachineNext g) state) : Option Term :=
  runOnAccessible g ⟨state,accessible⟩

theorem runAccessible_unfold (state : MachineState g) (accessible : Acc (MachineNext g) state) :
    runAccessible g state accessible=
      match actual : machineStep g state with
      | .next next => runAccessible g next (accessible.inv actual)
      | .done term => some term
      | .failed _ => none := by
  exact runOnAccessible.eq_1 g ⟨state,accessible⟩

theorem runAccessible_of_fuel {fuel : Nat} {state : MachineState g} {term : Term}
    (accessible : Acc (MachineNext g) state) (run : machineFuel g fuel state=.done term) :
    runAccessible g state accessible=some term := by
  induction fuel generalizing state with
  | zero => cases run
  | succ fuel ih =>
    cases actual : machineStep g state with
    | next next =>
      have unfold : runAccessible g state accessible=
          runAccessible g next (accessible.inv actual) := by
        have equation := runAccessible_unfold g state accessible
        split at equation
        next other step =>
          have same := MachineStep.next.inj (actual.symm.trans step)
          cases same
          exact equation
        next result step => cases actual.symm.trans step
        next reason step => cases actual.symm.trans step
      rw [unfold]
      exact ih _ (by simpa only [machineFuel,actual] using run)
    | done result =>
      have equal : result=term := by simpa only [machineFuel,actual,MachineRun.done.injEq] using run
      have equation := runAccessible_unfold g state accessible
      split at equation
      next other step => cases actual.symm.trans step
      next result step =>
        have same := MachineStep.done.inj (actual.symm.trans step)
        cases same
        simpa only [equal] using equation
      next reason step => cases actual.symm.trans step
    | failed reason =>
      simp only [machineFuel,actual] at run
      cases run

/-- This generic computational wrapper still requires a proved domain of
successful execution. P10 must construct that proposition from the effective
reachable-graph domain; it is not a substitute for its termination theorem. -/
def runCertified (state : MachineState g)
    (terminates : ∃ fuel term,machineFuel g fuel state=.done term) : Term :=
  let accessible : Acc (MachineNext g) state := by
    obtain ⟨fuel,term,run⟩ := terminates
    exact accessible_of_fuel g run
  let output := runAccessible g state accessible
  output.get (by
    obtain ⟨fuel,term,run⟩ := terminates
    have success := runAccessible_of_fuel g accessible run
    change (runAccessible g state accessible).isSome
    rw [success]
    trivial)

theorem runCertified_of_fuel {fuel : Nat} {state : MachineState g} {term : Term}
    (terminates : ∃ n value,machineFuel g n state=.done value)
    (run : machineFuel g fuel state=.done term) : runCertified g state terminates=term := by
  unfold runCertified
  simp only [runAccessible_of_fuel g _ run,Option.get_some]

end
end Lamping.AG.Readback
