import Lamping.Lamping.ReadbackPhysicalCursorAccess

namespace Lamping.AG.Readback.OccurrenceData.Unbounded
open Graph Lambda

private instance signatureKindEquality : DecidableEq signature.Kind :=
  inferInstanceAs (DecidableEq Kind)

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable [DecidableEq N] [DecidableEq B] [DecidableEq W]
variable {g : Net signature N B W}

/-- Only the actual empty/singleton stack can emit done. No semantic state
certificate is supplied by a caller. -/
theorem step_done_state {state : State g} {tree : Tree g}
    (actual : step g state=.done tree) : state=⟨[],[tree]⟩ := by
  rcases state with ⟨pending,values⟩
  cases pending with
  | nil =>
    cases values with
    | nil => cases actual
    | cons result values =>
      cases values with
      | nil =>
        have same : result=tree := Result.done.inj actual
        cases same
        rfl
      | cons second rest => cases actual
  | cons task rest =>
    cases task with
    | buildApp cursor =>
      cases values with
      | nil => cases actual
      | cons argument values => cases values <;> cases actual
    | buildLam cursor => cases values <;> cases actual
    | read departure context stem frames =>
      simp only [step] at actual
      split at actual
      next reason scanned => cases actual
      next nextDeparture output scanned => cases actual
      next arrival kind output scanned =>
        split at actual <;> (split at actual <;> cases actual)

/-- Finite execution evidence exists in Prop; the ordinary annotated run
continues to compute its own answer independently of this witness. -/
theorem run_success_has_fuel (state : AccessibleState g) {tree : Tree g}
    (success : runOnAccessible g state=some tree) :
    ∃ n,fuel g n state.val=.done tree := by
  cases actual : step g state.val with
  | next after =>
    have old := step_next_original actual
    have equation : runOnAccessible g state=
        runOnAccessible g ⟨after,state.property.inv old⟩ := by
      have unfolded := run_unfold g state.val state.property
      split at unfolded
      next other otherStep =>
        have same := Result.next.inj (actual.symm.trans otherStep)
        cases same
        exact unfolded
      next result otherStep => cases actual.symm.trans otherStep
      next reason otherStep => cases actual.symm.trans otherStep
    have tailSuccess := equation.symm.trans success
    obtain ⟨n,run⟩ := run_success_has_fuel ⟨after,state.property.inv old⟩ tailSuccess
    exact ⟨n+1,by simpa only [fuel,actual] using run⟩
  | done result =>
    have equation : runOnAccessible g state=some result := by
      have unfolded := run_unfold g state.val state.property
      split at unfolded
      next other otherStep => cases actual.symm.trans otherStep
      next other otherStep =>
        have same := Result.done.inj (actual.symm.trans otherStep)
        cases same
        exact unfolded
      next reason otherStep => cases actual.symm.trans otherStep
    have same := Option.some.inj (equation.symm.trans success)
    cases same
    exact ⟨1,by simp only [fuel,actual]⟩
  | failed reason =>
    have equation : runOnAccessible g state=none := by
      have unfolded := run_unfold g state.val state.property
      split at unfolded
      next other otherStep => cases actual.symm.trans otherStep
      next result otherStep => cases actual.symm.trans otherStep
      next other otherStep => exact unfolded
    have impossible := equation.symm.trans success
    cases impossible
termination_by state
decreasing_by exact step_next_original actual

theorem fuel_done_steps {n : Nat} {state : State g} {tree : Tree g}
    (run : fuel g n state=.done tree) : ∃ k,Steps g k state ⟨[],[tree]⟩ := by
  induction n generalizing state with
  | zero => cases run
  | succ n ih =>
    cases actual : step g state with
    | next after =>
      have tail : fuel g n after=.done tree := by
        simpa only [fuel,actual] using run
      obtain ⟨k,trace⟩ := ih tail
      exact ⟨k+1,.cons actual trace⟩
    | done result =>
      have same : result=tree := by
        simpa only [fuel,actual,Run.done.injEq] using run
      cases same
      cases step_done_state actual
      exact ⟨0,.refl _⟩
    | failed reason =>
      simp only [fuel,actual] at run
      cases run

theorem successful_run_steps {state : State g} {tree : Tree g}
    (accessible : Acc (MachineNext g) state.erase)
    (success : runOnAccessible g ⟨state,accessible⟩=some tree) :
    ∃ n,Steps g n state ⟨[],[tree]⟩ := by
  obtain ⟨n,run⟩ := run_success_has_fuel ⟨state,accessible⟩ success
  exact fuel_done_steps run

theorem initial_success_cursor_word {root : B} {tree : Tree g}
    (accessible : Acc (MachineNext g) (initial g root).erase)
    (success : runOnAccessible g ⟨initial g root,accessible⟩=some tree)
    {p : Path} {cursor : Sigma (Cursor g)} (located : tree.cursorAt p=some cursor) :
    accessWord g cursor.2.path=p := by
  obtain ⟨n,trace⟩ := successful_run_steps accessible success
  exact WordStack.initial_terminal_cursor_word trace located

theorem initial_success_cursor_framed {root : B} {tree : Tree g}
    (accessible : Acc (MachineNext g) (initial g root).erase)
    (success : runOnAccessible g ⟨initial g root,accessible⟩=some tree)
    {p : Path} {cursor : Sigma (Cursor g)} (located : tree.cursorAt p=some cursor) :
    Physical.CursorFramed root cursor.2 := by
  obtain ⟨n,trace⟩ := successful_run_steps accessible success
  exact Physical.initial_cursor_framed trace located

/-- No finite execution witness is extracted into the returned data. The
value is fixed by the already computed cursor before proving its access law. -/
def initial_success_cursor_access {root : B} {tree : Tree g}
    (accessible : Acc (MachineNext g) (initial g root).erase)
    (success : runOnAccessible g ⟨initial g root,accessible⟩=some tree)
    {p : Path} {cursor : Sigma (Cursor g)} (located : tree.cursorAt p=some cursor) :
    RootAccess g root :=
  Physical.CursorFramed.rootAccess cursor.2 (by
    obtain ⟨n,trace⟩ := successful_run_steps accessible success
    exact Physical.initial_cursor_framed trace located)

theorem initial_success_cursor_access_path {root : B} {tree : Tree g}
    (accessible : Acc (MachineNext g) (initial g root).erase)
    (success : runOnAccessible g ⟨initial g root,accessible⟩=some tree)
    {p : Path} {cursor : Sigma (Cursor g)} (located : tree.cursorAt p=some cursor) :
    (initial_success_cursor_access accessible success located).val=cursor.2.path := rfl

#print axioms Lamping.AG.Readback.OccurrenceData.Unbounded.step_done_state
#print axioms Lamping.AG.Readback.OccurrenceData.Unbounded.run_success_has_fuel
#print axioms Lamping.AG.Readback.OccurrenceData.Unbounded.fuel_done_steps
#print axioms Lamping.AG.Readback.OccurrenceData.Unbounded.successful_run_steps
#print axioms Lamping.AG.Readback.OccurrenceData.Unbounded.initial_success_cursor_word
#print axioms Lamping.AG.Readback.OccurrenceData.Unbounded.initial_success_cursor_framed
#print axioms Lamping.AG.Readback.OccurrenceData.Unbounded.initial_success_cursor_access
#print axioms Lamping.AG.Readback.OccurrenceData.Unbounded.initial_success_cursor_access_path

end
end Lamping.AG.Readback.OccurrenceData.Unbounded
