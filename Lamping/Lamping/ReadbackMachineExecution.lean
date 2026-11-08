import Lamping.Lamping.ReadbackMachine
import Lamping.Lamping.ReadbackScanSimulation

namespace Lamping.AG.Readback
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable [DecidableEq N] [DecidableEq B] [DecidableEq W]
variable (g : Net signature N B W)

/-- Exact finite next transitions, with no semantic certificate on states. -/
inductive MachineSteps : Nat → MachineState g → MachineState g → Prop where
  | refl (state) : MachineSteps 0 state state
  | cons {n before middle after} (step : machineStep g before=.next middle)
      (tail : MachineSteps n middle after) : MachineSteps (n+1) before after

namespace MachineSteps
variable {g}
theorem append {n m before middle after} (first : MachineSteps g n before middle)
    (last : MachineSteps g m middle after) : MachineSteps g (n+m) before after := by
  induction first with
  | refl => simpa only [Nat.zero_add] using last
  | @cons n before middle final step tail ih =>
    have size : (n+1)+m=(n+m)+1 := by omega
    rw [size]
    exact .cons step (ih last)

theorem fuel_more {n before after} (steps : MachineSteps g n before after) (extra : Nat) :
    machineFuel g (n+extra) before=machineFuel g extra after := by
  induction steps with
  | refl => simp only [Nat.zero_add]
  | cons step tail ih => simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,machineFuel,step] using ih

theorem fuel_exhausted {n before after} (steps : MachineSteps g n before after) :
    machineFuel g n before=.exhausted after := by
  simpa only [Nat.add_zero,machineFuel] using steps.fuel_more 0
end MachineSteps

/-- A finite scanner trace is data so its literal departures are available
without choice. Every constructor is an actual executable scanOne result. -/
inductive ScanSteps : Nat → Endpoint g → ContextData → Endpoint g → ContextData → Type where
  | refl (e a) : ScanSteps 0 e a e a
  | cons {n e a f b last output} (step : scanOne g e a=.next f b)
      (tail : ScanSteps n f b last output) : ScanSteps (n+1) e a last output

namespace ScanSteps
variable {g}
def departures {n e a f b} : ScanSteps g n e a f b → List (Endpoint g)
  | .refl _ _ => []
  | .cons (e:=e) _ tail => e::departures tail

omit [DecidableEq N] [DecidableEq B] [DecidableEq W] in
theorem departures_length {n e a f b} (trace : ScanSteps g n e a f b) : trace.departures.length=n := by
  induction trace with
  | refl => rfl
  | cons _ tail ih => simp only [departures,List.length_cons,ih]

omit [DecidableEq N] [DecidableEq B] [DecidableEq W] in
theorem literal_path {n e a f b} (trace : ScanSteps g n e a f b) :
    (trace.departures++[f]).head?=some e ∧(trace.departures++[f]).getLast?=some f := by
  cases trace with
  | refl => exact ⟨rfl,rfl⟩
  | cons => exact ⟨rfl,by simp⟩

omit [DecidableEq N] [DecidableEq B] [DecidableEq W] in
theorem scanFuel {n e a f b} (trace : ScanSteps g n e a f b) :
    scanFuel g (n+1) e a=scanFuel g 1 f b := by
  induction trace with
  | refl => rfl
  | cons step tail ih => simpa only [Readback.scanFuel,step] using ih

theorem machineSteps {n e a f b} (trace : ScanSteps g n e a f b)
    (stem : List (Endpoint g)) (frames : List (BinderFrame g))
    (rest : List (ReadbackTask g)) (values : List Term) :
    MachineSteps g n ⟨.read e a stem frames::rest,values⟩
      ⟨.read f b (stem++trace.departures) frames::rest,values⟩ := by
  induction trace generalizing stem with
  | refl => simpa only [departures,List.append_nil] using MachineSteps.refl (g:=g) _
  | @cons n e a f b last output step tail ih =>
    have first : machineStep g ⟨.read e a stem frames::rest,values⟩=
        .next ⟨.read f b (stem++[e]) frames::rest,values⟩ := by
      simp only [machineStep,step]
    have result := MachineSteps.cons first (ih (stem++[e]))
    simpa only [departures,List.append_assoc,List.singleton_append] using result
end ScanSteps

/- Construct scanner steps from one supplied finite control path. Its
literal list is retained; no graph-size bound or alternative route is used. -/
omit [DecidableEq N] [DecidableEq B] [DecidableEq W] in
theorem scanSteps_of_control_path {es : List (Endpoint g)} {before after : Context}
    (labels : Labelling g es before after)
    (controls : ∀ e f,(e,f)∈es.zip es.tail →ControlOnlyTurn (g:=g) e f)
    (first : Endpoint g) (head : es.head?=some first)
    (data : ContextData) (input : Context.ofList data=before) :
    ∃ (output : ContextData) (last : Endpoint g) (trace : ScanSteps g (es.length-1) first data last output),
      Context.ofList output=after ∧trace.departures++[last]=es := by
  induction labels generalizing first data with
  | single e before =>
    have same : e=first := by simpa using head
    subst first
    exact ⟨data,e,.refl _ _,input,rfl⟩
  | @cons e f es before middle after turn tail ih =>
    have same : e=first := by simpa using head
    subst first
    obtain ⟨middleData,step,contextEq⟩ := scanOne_next_complete turn (controls e f (by simp)) data input
    have tailControls : ∀ x y,(x,y)∈(f::es).zip (f::es).tail →ControlOnlyTurn (g:=g) x y := by
      intro x y member
      apply controls x y
      simp only [List.tail_cons,List.zip_cons_cons]
      exact List.mem_cons.mpr (Or.inr member)
    obtain ⟨output,last,trace,outputEq,literal⟩ := ih tailControls f rfl middleData contextEq
    have lengthEq : (e::f::es).length-1=((f::es).length-1)+1 := by simp
    rw [lengthEq]
    exact ⟨output,last,.cons step trace,outputEq,by simpa only [ScanSteps.departures,List.cons_append] using congrArg (e::·) literal⟩

end
end Lamping.AG.Readback
