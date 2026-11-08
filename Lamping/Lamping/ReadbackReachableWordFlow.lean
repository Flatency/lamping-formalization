import Lamping.Lamping.ReadbackWordStack

namespace Lamping.AG.Readback.OccurrenceData.WordStack
open Graph Lambda

private instance signatureKindEquality : DecidableEq signature.Kind :=
  inferInstanceAs (DecidableEq Kind)

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable [DecidableEq N] [DecidableEq B] [DecidableEq W]
variable {g : Net signature N B W}

theorem Invariant.read_app {final : Path} (cursor : Cursor g .app)
    (sort : (g.label cursor.arrival.1).sort=.op .app)
    (rest : List (Task g)) (values : List (Tree g))
    (inv : Invariant final ⟨.read cursor.departure cursor.input cursor.stem cursor.frames::rest,values⟩) :
    step g ⟨.read cursor.departure cursor.input cursor.stem cursor.frames::rest,values⟩=
        .next (appAfter cursor sort rest values) ∧
      Invariant final (appAfter cursor sort rest values) := by
  refine ⟨app_schedules cursor sort rest values,inv.1,?_⟩
  have tail := StackFlow.read_inv inv.2
  change StackFlow g rest (accessWord g cursor.path::values.map rootWord) final at tail
  have built : StackFlow g (.buildApp cursor::rest)
      ((accessWord g cursor.path++[.arg])::(accessWord g cursor.path++[.fn])::values.map rootWord) final :=
    .app tail
  have argument : StackFlow g
      (.read (argumentDeparture cursor sort) cursor.output cursor.path cursor.frames::
        .buildApp cursor::rest)
      ((accessWord g cursor.path++[.fn])::values.map rootWord) final := by
    apply StackFlow.read
    simpa only [readWord,(app_child_words cursor sort).2] using built
  change StackFlow g
    (.read (functionDeparture cursor sort) cursor.output cursor.path cursor.frames::
      .read (argumentDeparture cursor sort) cursor.output cursor.path cursor.frames::
      .buildApp cursor::rest) (values.map rootWord) final
  apply StackFlow.read
  simpa only [readWord,(app_child_words cursor sort).1] using argument

theorem Invariant.read_lam {final : Path} (cursor : Cursor g .lam)
    (sort : (g.label cursor.arrival.1).sort=.op .lam)
    (rest : List (Task g)) (values : List (Tree g))
    (inv : Invariant final ⟨.read cursor.departure cursor.input cursor.stem cursor.frames::rest,values⟩) :
    step g ⟨.read cursor.departure cursor.input cursor.stem cursor.frames::rest,values⟩=
        .next (lamAfter cursor sort rest values) ∧
      Invariant final (lamAfter cursor sort rest values) := by
  refine ⟨lam_schedules cursor sort rest values,inv.1,?_⟩
  have tail := StackFlow.read_inv inv.2
  change StackFlow g rest (accessWord g cursor.path::values.map rootWord) final at tail
  have built : StackFlow g (.buildLam cursor::rest)
      ((accessWord g cursor.path++[.body])::values.map rootWord) final := .lam tail
  change StackFlow g
    (.read (bodyDeparture cursor sort) cursor.output cursor.path
      (pushedFrame cursor sort::cursor.frames)::.buildLam cursor::rest)
      (values.map rootWord) final
  apply StackFlow.read
  simpa only [readWord,lam_child_word cursor sort] using built

private theorem var_schedules (cursor : Cursor g .var) (index : Nat)
    (selected : binderCandidates g cursor.frames cursor.arrival.1 cursor.path cursor.output=[index])
    (rest : List (Task g)) (values : List (Tree g)) :
    step g ⟨.read cursor.departure cursor.input cursor.stem cursor.frames::rest,values⟩=
      .next ⟨rest,.var cursor index::values⟩ := by
  rcases cursor with ⟨departure,input,stem,frames,arrival,output,actual⟩
  change binderCandidates g frames arrival.1 (stem++[departure]) output=[index] at selected
  simp only [step]
  split
  next reason scanned => cases actual.symm.trans scanned
  next nextDeparture nextContext scanned => cases actual.symm.trans scanned
  next otherArrival otherKind otherOutput scanned =>
    obtain ⟨rfl,rfl,rfl⟩ := ScanResult.terminal.inj (actual.symm.trans scanned)
    split <;> first
    | contradiction
    | (simp_all only [] <;> rfl)

theorem Invariant.read_var {final : Path} (cursor : Cursor g .var) (index : Nat)
    (selected : binderCandidates g cursor.frames cursor.arrival.1 cursor.path cursor.output=[index])
    (rest : List (Task g)) (values : List (Tree g))
    (inv : Invariant final ⟨.read cursor.departure cursor.input cursor.stem cursor.frames::rest,values⟩) :
    step g ⟨.read cursor.departure cursor.input cursor.stem cursor.frames::rest,values⟩=
        .next ⟨rest,.var cursor index::values⟩ ∧
      Invariant final ⟨rest,.var cursor index::values⟩ := by
  refine ⟨var_schedules cursor index selected rest values,?_,?_⟩
  · intro tree member
    rcases List.mem_cons.mp member with same | previous
    · cases same
      exact True.intro
    · exact inv.1 tree previous
  · simpa only [List.map_cons,rootWord,readWord,Cursor.path] using StackFlow.read_inv inv.2

/-- All actual next transitions preserve the internal whole-stack proof state.
No expected cursor position, physical access, or frame certificate is supplied. -/
theorem Invariant.next {final : Path} {before after : State g}
    (inv : Invariant final before) (actual : step g before=.next after) :
    Invariant final after := by
  rcases before with ⟨pending,values⟩
  cases pending with
  | nil =>
    cases values with
    | nil => cases actual
    | cons tree values => cases values <;> cases actual
  | cons task rest =>
    cases task with
    | buildApp cursor =>
      cases values with
      | nil => cases actual
      | cons argument values =>
        cases values with
        | nil => cases actual
        | cons function values =>
          have law := Invariant.build_app cursor function argument rest values inv
          have same := Result.next.inj (law.1.symm.trans actual)
          cases same
          exact law.2
    | buildLam cursor =>
      cases values with
      | nil => cases actual
      | cons body values =>
        have law := Invariant.build_lam cursor body rest values inv
        have same := Result.next.inj (law.1.symm.trans actual)
        cases same
        exact law.2
    | read departure input stem frames =>
      have original := step_next_original actual
      change machineStep g
        ⟨ReadbackTask.read departure input stem frames::rest.map Task.erase,values.map Tree.erase⟩=
          .next after.erase at original
      cases scanned : scanOne g departure input with
      | failed reason => simp [machineStep,scanned] at original
      | next nextDeparture output =>
        have law := Invariant.scan_next scanned stem frames rest values inv
        have same := Result.next.inj (law.1.symm.trans actual)
        cases same
        exact law.2
      | terminal arrival kind output =>
        cases kind with
        | app =>
          by_cases sort : (g.label arrival.1).sort=.op .app
          · let cursor : Cursor g .app := ⟨departure,input,stem,frames,arrival,output,scanned⟩
            have law := Invariant.read_app cursor sort rest values inv
            have same := Result.next.inj (law.1.symm.trans actual)
            cases same
            exact law.2
          · simp [machineStep,scanned,sort] at original
        | lam =>
          by_cases sort : (g.label arrival.1).sort=.op .lam
          · let cursor : Cursor g .lam := ⟨departure,input,stem,frames,arrival,output,scanned⟩
            have law := Invariant.read_lam cursor sort rest values inv
            have same := Result.next.inj (law.1.symm.trans actual)
            cases same
            exact law.2
          · simp [machineStep,scanned,sort] at original
        | var =>
          cases candidates : binderCandidates g frames arrival.1 (stem++[departure]) output with
          | nil => simp [machineStep,scanned,candidates] at original
          | cons index indices =>
            cases indices with
            | nil =>
              let cursor : Cursor g .var := ⟨departure,input,stem,frames,arrival,output,scanned⟩
              have law := Invariant.read_var cursor index candidates rest values inv
              have same := Result.next.inj (law.1.symm.trans actual)
              cases same
              exact law.2
            | cons second more => simp [machineStep,scanned,candidates] at original

theorem Invariant.steps {final : Path} {n : Nat} {before after : State g}
    (inv : Invariant final before) (trace : Steps g n before after) :
    Invariant final after := by
  revert inv
  induction trace with
  | refl => intro inv; exact inv
  | cons actual _tail ih =>
    intro inv
    exact ih (inv.next actual)

theorem initial_steps_invariant {root : B} {n : Nat} {after : State g}
    (trace : Steps g n (initial g root) after) : Invariant [] after :=
  (initial_invariant root).steps trace

/-- Caller-free position-word correctness for a genuinely completed initial
execution. Actual Steps is the only run premise; no final invariant is supplied. -/
theorem initial_terminal_cursor_word {root : B} {n : Nat} {tree : Tree g}
    (trace : Steps g n (initial g root) ⟨[],[tree]⟩) {p : Path}
    {cursor : Sigma (Cursor g)} (located : tree.cursorAt p=some cursor) :
    accessWord g cursor.2.path=p := by
  have invariant := initial_steps_invariant trace
  simpa only [List.nil_append] using invariant.terminal_cursor_word located

#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.Invariant.read_app
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.Invariant.read_lam
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.Invariant.read_var
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.Invariant.next
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.Invariant.steps
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.initial_steps_invariant
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.initial_terminal_cursor_word

end
end Lamping.AG.Readback.OccurrenceData.WordStack
