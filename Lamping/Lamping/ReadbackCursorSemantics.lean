import Lamping.Lamping.ReadbackOccurrenceData
import Lamping.Lamping.ReadbackTermination

namespace Lamping.AG.Readback.OccurrenceData
open Graph Lambda

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable [DecidableEq N] [DecidableEq B] [DecidableEq W]

theorem step_next_original {g : Net signature N B W} {state next : State g}
    (actual : step g state=.next next) : MachineNext g next.erase state.erase := by
  change machineStep g state.erase=.next next.erase
  simpa only [actual,Result.erase] using (step_erase g state).symm

theorem run_unfold (g : Net signature N B W) (state : State g)
    (accessible : Acc (MachineNext g) state.erase) :
    runOnAccessible g ⟨state,accessible⟩ =
      match actual : step g state with
      | .next next => runOnAccessible g ⟨next,accessible.inv (step_next_original actual)⟩
      | .done tree => some tree
      | .failed _ => none := by
  exact runOnAccessible.eq_1 g ⟨state,accessible⟩

/-- Actual finite annotation trace determines this ordinary unbounded run;
no fuel witness is eliminated into the program's output type. -/
theorem run_of_fuel {g : Net signature N B W} {n : Nat} {state : State g}
    {tree : Tree g} (accessible : Acc (MachineNext g) state.erase)
    (run : fuel g n state=.done tree) :
    runOnAccessible g ⟨state,accessible⟩=some tree := by
  induction n generalizing state with
  | zero => cases run
  | succ n ih =>
    cases actual : step g state with
    | next next =>
      have unfold : runOnAccessible g ⟨state,accessible⟩=
          runOnAccessible g ⟨next,accessible.inv (step_next_original actual)⟩ := by
        have equation := run_unfold g state accessible
        split at equation
        next other otherStep =>
          have same := Result.next.inj (actual.symm.trans otherStep)
          cases same
          exact equation
        next result otherStep => cases actual.symm.trans otherStep
        next reason otherStep => cases actual.symm.trans otherStep
      rw [unfold]
      exact ih _ (by simpa only [fuel,actual] using run)
    | done result =>
      have same : result=tree := by simpa only [fuel,actual,Run.done.injEq] using run
      have equation := run_unfold g state accessible
      split at equation
      next other otherStep => cases actual.symm.trans otherStep
      next result otherStep =>
        have equal := Result.done.inj (actual.symm.trans otherStep)
        cases equal
        simpa only [same] using equation
      next reason otherStep => cases actual.symm.trans otherStep
    | failed reason =>
      simp only [fuel,actual] at run
      cases run

/-- This existence is in Prop. The annotated fuel function itself already
computes the tree, and the ordinary run above needs no chosen fuel as data. -/
theorem original_done_lifts {g : Net signature N B W} {n : Nat} {state : State g}
    {term : Term} (run : machineFuel g n state.erase=.done term) :
    ∃ tree : Tree g,fuel g n state=.done tree ∧ tree.erase=term := by
  have erased : (fuel g n state).erase=.done term := (fuel_erase g n state).trans run
  cases actual : fuel g n state with
  | exhausted after =>
    have impossible : (MachineRun.exhausted after.erase : MachineRun g)=.done term := by
      simpa only [actual,Run.erase] using erased
    cases impossible
  | failed reason =>
    have impossible : (MachineRun.failed reason : MachineRun g)=.done term := by
      simpa only [actual,Run.erase] using erased
    cases impossible
  | done tree =>
    have same : tree.erase=term := MachineRun.done.inj (by
      simpa only [actual,Run.erase] using erased)
    exact ⟨tree,rfl,same⟩

theorem successful_run_erasure {g : Net signature N B W} {n : Nat}
    {state : State g} {term : Term} (accessible : Acc (MachineNext g) state.erase)
    (run : machineFuel g n state.erase=.done term) :
    (runOnAccessible g ⟨state,accessible⟩).map Tree.erase =
      Lamping.AG.Readback.runAccessible g state.erase accessible := by
  obtain ⟨tree,annotated,same⟩ := original_done_lifts run
  have newRun := run_of_fuel accessible annotated
  rw [newRun,Option.map_some,same,Lamping.AG.Readback.runAccessible_of_fuel g accessible run]

/-- Existing P10 halting supplies only the erased accessibility proof. The
annotated executable run itself computes its successful output and provenance. -/
theorem initial_success {g : Net signature N B W} {root : B} {term : Term}
    (matching : Matches g root term) (inputs : RootInputs g root)
    (transparency : Transparency g root) :
    ∃ (accessible : Acc (MachineNext g) (initial g root).erase) (tree : Tree g),
      runOnAccessible g ⟨initial g root,accessible⟩=some tree ∧ tree.erase=term := by
  obtain ⟨n,run⟩ := Lamping.AG.Readback.readbackFuel_terminates matching inputs transparency
  have original : machineFuel g n (initial g root).erase=.done term := by
    simpa only [initial_erase,readbackFuel] using run
  let accessible := accessible_of_fuel g original
  obtain ⟨tree,annotated,same⟩ := original_done_lifts original
  exact ⟨accessible,tree,run_of_fuel accessible annotated,same⟩

variable {g : Net signature N B W} {root : B} {n : Nat}
variable {last : Endpoint g} {context output : ContextData}
variable {arrival : NodePort signature N g.label} {kind : AccessKind}

/-- Actual annotated machine transitions, with no semantic access fields. -/
inductive Steps (g : Net signature N B W) : Nat → State g → State g → Prop where
  | refl (state) : Steps g 0 state state
  | cons {n before middle after} (actual : step g before=.next middle)
      (tail : Steps g n middle after) : Steps g (n+1) before after

theorem scan_advances {e f : Endpoint g} {a b : ContextData} {k : Nat}
    (trace : ScanSteps g k e a f b) (stem : List (Endpoint g))
    (frames : List (BinderFrame g)) (rest : List (Task g)) (values : List (Tree g)) :
    Steps g k ⟨.read e a stem frames::rest,values⟩
      ⟨.read f b (stem++trace.departures) frames::rest,values⟩ := by
  induction trace generalizing stem with
  | refl => simpa only [ScanSteps.departures,List.append_nil] using Steps.refl (g:=g) _
  | @cons n e a f b last output actual tail ih =>
    have first : step g ⟨.read e a stem frames::rest,values⟩=
        .next ⟨.read f b (stem++[e]) frames::rest,values⟩ := by
      simp only [step]
      split
      next reason scanned => cases actual.symm.trans scanned
      next nextDeparture nextContext scanned =>
        obtain ⟨rfl,rfl⟩ := ScanResult.next.inj (actual.symm.trans scanned)
        rfl
      next arrival kind after scanned => cases actual.symm.trans scanned
    have result := Steps.cons first (ih (stem++[e]))
    simpa only [ScanSteps.departures,List.append_assoc,List.singleton_append] using result

theorem initial_scan_steps
    (trace : ScanSteps g n (.inr (.inl root)) [] last context) :
    Steps g n (initial g root) ⟨[.read last context trace.departures []],[]⟩ := by
  simpa only [initial,List.nil_append] using scan_advances trace [] [] [] []

/-- A cursor computed directly from a real initial scanner trace. Its only
proof input describes the actual final scanner result, not a semantic access. -/
def rootScanCursor (trace : ScanSteps g n (.inr (.inl root)) [] last context)
    (terminal : scanOne g last context=.terminal arrival kind output) : Cursor g kind :=
  ⟨last,context,trace.departures,[],arrival,output,terminal⟩

omit [DecidableEq N] [DecidableEq B] [DecidableEq W] in
theorem rootScanCursor_path
    (trace : ScanSteps g n (.inr (.inl root)) [] last context)
    (terminal : scanOne g last context=.terminal arrival kind output) :
    (rootScanCursor trace terminal).path=trace.departures++[last] := rfl

omit [DecidableEq N] [DecidableEq B] [DecidableEq W] in
theorem rootScanCursor_framed
    (trace : ScanSteps g n (.inr (.inl root)) [] last context)
    (terminal : scanOne g last context=.terminal arrival kind output) :
    FramedPath g root [] (rootScanCursor trace terminal).path context [] := by
  have start : FramedPath g root [] ([]++[.inr (.inl root)]) [] [] := .initial
  have result := trace.framed [] [] [] start
  simpa only [rootScanCursor,Cursor.path,List.nil_append] using result

omit [DecidableEq N] [DecidableEq B] [DecidableEq W] in
theorem rootScanCursor_labels
    (trace : ScanSteps g n (.inr (.inl root)) [] last context)
    (terminal : scanOne g last context=.terminal arrival kind output) :
    Labelling g (rootScanCursor trace terminal).path
      (Context.ofList []) (Context.ofList output) := by
  have same : output=context := (scanOne_terminal_sound g last arrival kind context output terminal).2.2
  cases same
  exact (rootScanCursor_framed trace terminal).labels

/-- The whole initial root access is built from actual trace data. This is
not obtained from Matches.actual_redex_access or from a supplied RootAccess. -/
def rootScanAccess
    (trace : ScanSteps g n (.inr (.inl root)) [] last context)
    (terminal : scanOne g last context=.terminal arrival kind output) : RootAccess g root :=
  ⟨(rootScanCursor trace terminal).path,by
    have framed := rootScanCursor_framed trace terminal
    obtain ⟨finish,role,_same⟩ := scanOne_terminal_sound g last arrival kind context output terminal
    refine ⟨⟨⟨_,_,framed.labels⟩,framed.forward⟩,framed.rooted,kind,?_⟩
    have lastEq : (rootScanCursor trace terminal).path.getLast?=some last := by
      simp only [rootScanCursor,Cursor.path,List.getLast?_append,List.getLast?_singleton,Option.some_or]
    unfold accessKind
    rw [lastEq]
    simp only [Option.bind_some,finish]
    exact role⟩

omit [DecidableEq N] [DecidableEq B] [DecidableEq W] in
theorem rootScanAccess_path
    (trace : ScanSteps g n (.inr (.inl root)) [] last context)
    (terminal : scanOne g last context=.terminal arrival kind output) :
    (rootScanAccess trace terminal).val=(rootScanCursor trace terminal).path := rfl

#print axioms Lamping.AG.Readback.OccurrenceData.step_next_original
#print axioms Lamping.AG.Readback.OccurrenceData.run_unfold
#print axioms Lamping.AG.Readback.OccurrenceData.run_of_fuel
#print axioms Lamping.AG.Readback.OccurrenceData.original_done_lifts
#print axioms Lamping.AG.Readback.OccurrenceData.successful_run_erasure
#print axioms Lamping.AG.Readback.OccurrenceData.initial_success
#print axioms Lamping.AG.Readback.OccurrenceData.Steps
#print axioms Lamping.AG.Readback.OccurrenceData.scan_advances
#print axioms Lamping.AG.Readback.OccurrenceData.initial_scan_steps
#print axioms Lamping.AG.Readback.OccurrenceData.rootScanCursor
#print axioms Lamping.AG.Readback.OccurrenceData.rootScanCursor_path
#print axioms Lamping.AG.Readback.OccurrenceData.rootScanCursor_framed
#print axioms Lamping.AG.Readback.OccurrenceData.rootScanCursor_labels
#print axioms Lamping.AG.Readback.OccurrenceData.rootScanAccess
#print axioms Lamping.AG.Readback.OccurrenceData.rootScanAccess_path

end
end Lamping.AG.Readback.OccurrenceData
