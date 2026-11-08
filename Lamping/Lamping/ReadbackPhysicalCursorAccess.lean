import Lamping.Lamping.ReadbackReachableWordFlow

namespace Lamping.AG.Readback.OccurrenceData.Physical
open Graph Lambda

private instance signatureKindEquality : DecidableEq signature.Kind :=
  inferInstanceAs (DecidableEq Kind)

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

def CursorFramed (root : B) {kind : AccessKind} (cursor : Cursor g kind) : Prop :=
  FramedPath g root [] cursor.path cursor.input cursor.frames

def TreeFramed (root : B) : Tree g → Prop
  | .var cursor _ => CursorFramed root cursor
  | .app cursor function argument =>
      CursorFramed root cursor ∧ TreeFramed root function ∧ TreeFramed root argument
  | .lam cursor body => CursorFramed root cursor ∧ TreeFramed root body

def TaskFramed (root : B) : Task g → Prop
  | .read departure context stem frames =>
      FramedPath g root [] (stem++[departure]) context frames
  | .buildApp cursor => CursorFramed root cursor
  | .buildLam cursor => CursorFramed root cursor

def StateFramed (root : B) (state : State g) : Prop :=
  (∀ task∈state.pending, TaskFramed root task) ∧
    ∀ tree∈state.values, TreeFramed root tree

private theorem all_cons {α : Type} {P : α → Prop} {head : α} {tail : List α}
    (first : P head) (rest : ∀ x∈tail,P x) : ∀ x∈head::tail,P x := by
  intro x member
  rcases List.mem_cons.mp member with same | previous
  · cases same; exact first
  · exact rest x previous

private theorem last_cursor {kind : AccessKind} (cursor : Cursor g kind) :
    cursor.path.getLast?=some cursor.departure := by
  simp only [Cursor.path,List.getLast?_append,List.getLast?_singleton,Option.some_or]

private theorem cast_port {kind target : Kind} (sort : kind=target) (port : Port target) :
    HEq (sort.symm ▸ port) port := by subst target; rfl

private theorem app_context {kind : Kind} (port : Port kind) (sort : kind=.op .app)
    (role : portKind kind port=some .app) : HEq port appCtx := by
  subst kind
  cases port with
  | inl payload => cases payload; simp [portKind] at role
  | inr bit => cases bit <;> simp_all [portKind,appCtx]

private theorem lam_context {kind : Kind} (port : Port kind) (sort : kind=.op .lam)
    (role : portKind kind port=some .lam) :
    HEq port (Sum.inl () : Port (.op .lam)) := by
  subst kind
  cases port with
  | inl payload => cases payload; rfl
  | inr bit => cases bit <;> simp [portKind] at role

theorem CursorFramed.app_children {root : B} (cursor : Cursor g .app)
    (sort : (g.label cursor.arrival.1).sort=.op .app) (framed : CursorFramed root cursor) :
    FramedPath g root [] (cursor.path++[functionDeparture cursor sort]) cursor.output cursor.frames ∧
    FramedPath g root [] (cursor.path++[argumentDeparture cursor sort]) cursor.output cursor.frames := by
  have actual := scanOne_terminal_sound g cursor.departure cursor.arrival .app
    cursor.input cursor.output cursor.actual
  have current : FramedPath g root [] cursor.path cursor.output cursor.frames := by
    rw [actual.2.2]; exact framed
  constructor
  · exact .application current (last_cursor cursor) cursor.arrival.1 cursor.arrival.2
      (sort.symm ▸ (Sum.inl () : Port (.op .app))) sort
      (app_context cursor.arrival.2 sort actual.2.1)
      (Or.inl (cast_port sort _)) actual.1
  · exact .application current (last_cursor cursor) cursor.arrival.1 cursor.arrival.2
      (sort.symm ▸ appArg) sort (app_context cursor.arrival.2 sort actual.2.1)
      (Or.inr (cast_port sort _)) actual.1

theorem CursorFramed.lam_child {root : B} (cursor : Cursor g .lam)
    (sort : (g.label cursor.arrival.1).sort=.op .lam) (framed : CursorFramed root cursor) :
    FramedPath g root [] (cursor.path++[bodyDeparture cursor sort]) cursor.output
      (pushedFrame cursor sort::cursor.frames) := by
  have actual := scanOne_terminal_sound g cursor.departure cursor.arrival .lam
    cursor.input cursor.output cursor.actual
  have current : FramedPath g root [] cursor.path cursor.output cursor.frames := by
    rw [actual.2.2]; exact framed
  exact .body current (last_cursor cursor) cursor.arrival.1 cursor.arrival.2
    (sort.symm ▸ lamBody) sort (lam_context cursor.arrival.2 sort actual.2.1)
    (cast_port sort _) actual.1

/-- This data is the cursor's own path; the proof never selects another list. -/
def CursorFramed.rootAccess {root : B} {kind : AccessKind} (cursor : Cursor g kind)
    (framed : CursorFramed root cursor) : RootAccess g root :=
  ⟨cursor.path,by
    have actual := scanOne_terminal_sound g cursor.departure cursor.arrival kind
      cursor.input cursor.output cursor.actual
    refine ⟨⟨⟨_,_,framed.labels⟩,framed.forward⟩,framed.rooted,kind,?_⟩
    unfold accessKind
    rw [last_cursor cursor]
    simp only [Option.bind_some,actual.1]
    exact actual.2.1⟩

theorem TreeFramed.nodeAt {root : B} {tree sub : Tree g} {p : Path}
    (framed : TreeFramed root tree) (located : tree.nodeAt p=some sub) :
    TreeFramed root sub := by
  induction p generalizing tree with
  | nil =>
    have atRoot : tree.nodeAt []=some tree := by cases tree <;> rfl
    cases Option.some.inj (atRoot.symm.trans located)
    exact framed
  | cons direction p ih =>
    cases tree with
    | var cursor index => cases direction <;> simp [Tree.nodeAt] at located
    | app cursor function argument =>
      cases direction with
      | body => simp [Tree.nodeAt] at located
      | fn => exact ih framed.2.1 located
      | arg => exact ih framed.2.2 located
    | lam cursor body =>
      cases direction with
      | fn => simp [Tree.nodeAt] at located
      | arg => simp [Tree.nodeAt] at located
      | body => exact ih framed.2 located

theorem TreeFramed.cursorAt {root : B} {tree : Tree g} {p : Path}
    {cursor : Sigma (Cursor g)} (framed : TreeFramed root tree)
    (located : tree.cursorAt p=some cursor) : CursorFramed root cursor.2 := by
  obtain ⟨sub,atSub,same,_syntax⟩ := Tree.cursorAt_some located
  have subFramed := framed.nodeAt atSub
  have rootFramed : CursorFramed root sub.cursor.2 := by
    cases sub with
    | var cursor index => exact subFramed
    | app cursor function argument => exact subFramed.1
    | lam cursor body => exact subFramed.1
  cases same
  exact rootFramed

theorem initial_framed (root : B) : StateFramed root (initial g root) := by
  constructor
  · apply all_cons
    · exact FramedPath.initial
    · intro task member; cases member
  · intro tree member; cases member

section Execution
variable [DecidableEq N] [DecidableEq B] [DecidableEq W]

private theorem var_step (cursor : Cursor g .var) (index : Nat)
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

/-- All saved task cursors and all emitted tree cursors retain the actual
FramedPath, including the exact frame list pushed by lambda scheduling. -/
theorem StateFramed.next {root : B} {before after : State g}
    (invariant : StateFramed root before) (actual : step g before=.next after) :
    StateFramed root after := by
  rcases before with ⟨pending,values⟩
  cases pending with
  | nil => cases values with
    | nil => cases actual
    | cons tree values => cases values <;> cases actual
  | cons task rest =>
    have first := invariant.1 task (by simp)
    have remaining : ∀ other∈rest,TaskFramed root other := by
      intro other member; exact invariant.1 other (List.mem_cons_of_mem _ member)
    cases task with
    | buildApp cursor =>
      cases values with
      | nil => cases actual
      | cons argument values => cases values with
        | nil => cases actual
        | cons function values =>
          have same : (⟨rest,.app cursor function argument::values⟩ : State g)=after :=
            Result.next.inj actual
          cases same
          refine ⟨remaining,all_cons ⟨first,?_,?_⟩ ?_⟩
          · exact invariant.2 function (by simp)
          · exact invariant.2 argument (by simp)
          · intro tree member
            exact invariant.2 tree (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
    | buildLam cursor =>
      cases values with
      | nil => cases actual
      | cons body values =>
        have same : (⟨rest,.lam cursor body::values⟩ : State g)=after := Result.next.inj actual
        cases same
        refine ⟨remaining,all_cons ⟨first,invariant.2 body (by simp)⟩ ?_⟩
        intro tree member; exact invariant.2 tree (List.mem_cons_of_mem _ member)
    | read departure input stem frames =>
      have original := step_next_original actual
      change machineStep g
        ⟨ReadbackTask.read departure input stem frames::rest.map Task.erase,values.map Tree.erase⟩=
          .next after.erase at original
      cases scanned : scanOne g departure input with
      | failed reason => simp [machineStep,scanned] at original
      | next nextDeparture output =>
        let one : ScanSteps g 1 departure input nextDeparture output :=
          .cons scanned (.refl _ _)
        have framed := one.framed [] stem frames first
        have law : step g ⟨.read departure input stem frames::rest,values⟩=
            .next ⟨.read nextDeparture output (stem++[departure]) frames::rest,values⟩ := by
          simp only [step]
          split
          next reason other => cases scanned.symm.trans other
          next d c other =>
            obtain ⟨rfl,rfl⟩ := ScanResult.next.inj (scanned.symm.trans other)
            rfl
          next arrival kind c other => cases scanned.symm.trans other
        cases Result.next.inj (law.symm.trans actual)
        refine ⟨all_cons ?_ remaining,invariant.2⟩
        simpa only [one,ScanSteps.departures] using framed
      | terminal arrival kind output =>
        cases kind with
        | app =>
          by_cases sort : (g.label arrival.1).sort=.op .app
          · let cursor : Cursor g .app := ⟨departure,input,stem,frames,arrival,output,scanned⟩
            have good : CursorFramed root cursor := first
            have children := CursorFramed.app_children cursor sort good
            have law := app_schedules cursor sort rest values
            cases Result.next.inj (law.symm.trans actual)
            exact ⟨all_cons children.1 (all_cons children.2 (all_cons good remaining)),invariant.2⟩
          · simp [machineStep,scanned,sort] at original
        | lam =>
          by_cases sort : (g.label arrival.1).sort=.op .lam
          · let cursor : Cursor g .lam := ⟨departure,input,stem,frames,arrival,output,scanned⟩
            have good : CursorFramed root cursor := first
            have child := CursorFramed.lam_child cursor sort good
            have law := lam_schedules cursor sort rest values
            cases Result.next.inj (law.symm.trans actual)
            exact ⟨all_cons child (all_cons good remaining),invariant.2⟩
          · simp [machineStep,scanned,sort] at original
        | var =>
          cases candidates : binderCandidates g frames arrival.1 (stem++[departure]) output with
          | nil => simp [machineStep,scanned,candidates] at original
          | cons index indices => cases indices with
            | nil =>
              let cursor : Cursor g .var := ⟨departure,input,stem,frames,arrival,output,scanned⟩
              have good : CursorFramed root cursor := first
              have law := var_step cursor index candidates rest values
              cases Result.next.inj (law.symm.trans actual)
              exact ⟨remaining,all_cons good invariant.2⟩
            | cons second more => simp [machineStep,scanned,candidates] at original

theorem StateFramed.steps {root : B} {n : Nat} {before after : State g}
    (invariant : StateFramed root before) (trace : Steps g n before after) :
    StateFramed root after := by
  revert invariant
  induction trace with
  | refl => intro invariant; exact invariant
  | cons actual _tail ih =>
    intro invariant
    exact ih (invariant.next actual)

theorem initial_steps_framed {root : B} {n : Nat} {after : State g}
    (trace : Steps g n (initial g root) after) : StateFramed root after :=
  (initial_framed root).steps trace

theorem initial_cursor_framed {root : B} {n : Nat} {tree : Tree g}
    (trace : Steps g n (initial g root) ⟨[],[tree]⟩) {p : Path}
    {cursor : Sigma (Cursor g)} (located : tree.cursorAt p=some cursor) :
    CursorFramed root cursor.2 := by
  have invariant := initial_steps_framed trace
  exact (invariant.2 tree (by simp)).cursorAt located

/-- Caller-free physical access on the literal data cursor from the real run. -/
def initial_cursor_access {root : B} {n : Nat} {tree : Tree g}
    (trace : Steps g n (initial g root) ⟨[],[tree]⟩) {p : Path}
    {cursor : Sigma (Cursor g)} (located : tree.cursorAt p=some cursor) : RootAccess g root :=
  CursorFramed.rootAccess cursor.2 (initial_cursor_framed trace located)

theorem initial_cursor_access_path {root : B} {n : Nat} {tree : Tree g}
    (trace : Steps g n (initial g root) ⟨[],[tree]⟩) {p : Path}
    {cursor : Sigma (Cursor g)} (located : tree.cursorAt p=some cursor) :
    (initial_cursor_access trace located).val=cursor.2.path := rfl

end Execution

#print axioms Lamping.AG.Readback.OccurrenceData.Physical.CursorFramed
#print axioms Lamping.AG.Readback.OccurrenceData.Physical.TreeFramed
#print axioms Lamping.AG.Readback.OccurrenceData.Physical.TaskFramed
#print axioms Lamping.AG.Readback.OccurrenceData.Physical.StateFramed
#print axioms Lamping.AG.Readback.OccurrenceData.Physical.CursorFramed.app_children
#print axioms Lamping.AG.Readback.OccurrenceData.Physical.CursorFramed.lam_child
#print axioms Lamping.AG.Readback.OccurrenceData.Physical.CursorFramed.rootAccess
#print axioms Lamping.AG.Readback.OccurrenceData.Physical.TreeFramed.nodeAt
#print axioms Lamping.AG.Readback.OccurrenceData.Physical.TreeFramed.cursorAt
#print axioms Lamping.AG.Readback.OccurrenceData.Physical.initial_framed
#print axioms Lamping.AG.Readback.OccurrenceData.Physical.StateFramed.next
#print axioms Lamping.AG.Readback.OccurrenceData.Physical.StateFramed.steps
#print axioms Lamping.AG.Readback.OccurrenceData.Physical.initial_steps_framed
#print axioms Lamping.AG.Readback.OccurrenceData.Physical.initial_cursor_framed
#print axioms Lamping.AG.Readback.OccurrenceData.Physical.initial_cursor_access
#print axioms Lamping.AG.Readback.OccurrenceData.Physical.initial_cursor_access_path

end
end Lamping.AG.Readback.OccurrenceData.Physical
