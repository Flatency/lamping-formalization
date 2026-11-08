import Lamping.Lamping.ReadbackEffectiveRun

namespace Lamping.AG.Readback.OccurrenceData
open Graph Lambda

private instance signatureKindEquality : DecidableEq signature.Kind :=
  inferInstanceAs (DecidableEq Kind)

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable [DecidableEq N] [DecidableEq B] [DecidableEq W]

/-- Actual scan cursor. The equality is supplied by the executable terminal
match; it is erased and never selects a node, port, context, or syntax result. -/
structure Cursor (g : Net signature N B W) (kind : AccessKind) where
  departure : Endpoint g
  input : ContextData
  stem : List (Endpoint g)
  frames : List (BinderFrame g)
  arrival : NodePort signature N g.label
  output : ContextData
  actual : scanOne g departure input = .terminal arrival kind output

def Cursor.path {g : Net signature N B W} {kind : AccessKind}
    (cursor : Cursor g kind) : List (Endpoint g) := cursor.stem++[cursor.departure]

/-- A syntax tree retaining exactly one actual emitting cursor at each node. -/
inductive Tree (g : Net signature N B W) where
  | var (cursor : Cursor g .var) (index : Nat)
  | app (cursor : Cursor g .app) (function argument : Tree g)
  | lam (cursor : Cursor g .lam) (body : Tree g)

def Tree.erase {g : Net signature N B W} : Tree g → Term
  | .var _ i => .var i
  | .app _ f a => .app f.erase a.erase
  | .lam _ b => .lam b.erase

def Tree.cursor {g : Net signature N B W} : Tree g → Sigma (Cursor g)
  | .var c _ => ⟨.var,c⟩
  | .app c _ _ => ⟨.app,c⟩
  | .lam c _ => ⟨.lam,c⟩

def Tree.nodeAt {g : Net signature N B W} : Tree g → Path → Option (Tree g)
  | tree,[] => some tree
  | .app _ f _,.fn::p => f.nodeAt p
  | .app _ _ a,.arg::p => a.nodeAt p
  | .lam _ b,.body::p => b.nodeAt p
  | _,_ => none

def Tree.cursorAt {g : Net signature N B W} (tree : Tree g) (p : Path) :
    Option (Sigma (Cursor g)) := (tree.nodeAt p).map Tree.cursor

omit [DecidableEq N] [DecidableEq B] [DecidableEq W] in
theorem Tree.nodeAt_erase {g : Net signature N B W} (tree : Tree g) (p : Path) :
    (tree.nodeAt p).map Tree.erase = subtermAt tree.erase p := by
  induction p generalizing tree with
  | nil => cases tree <;> rfl
  | cons direction p ih =>
    cases tree <;> cases direction <;>
      simp only [Tree.nodeAt,Tree.erase,subtermAt,Option.map_none,ih]

omit [DecidableEq N] [DecidableEq B] [DecidableEq W] in
theorem Tree.cursorAt_some {g : Net signature N B W} {tree : Tree g} {p : Path}
    {cursor : Sigma (Cursor g)} (located : tree.cursorAt p=some cursor) :
    ∃ sub : Tree g, tree.nodeAt p=some sub ∧ sub.cursor=cursor ∧
      subtermAt tree.erase p=some sub.erase := by
  obtain ⟨sub,atSub,same⟩ := Option.map_eq_some_iff.mp located
  refine ⟨sub,atSub,same,?_⟩
  have erased := congrArg (Option.map Tree.erase) atSub
  rw [Tree.nodeAt_erase] at erased
  exact erased

/-- Compute both physical terminals of a syntax redex, preserving all cursor
data. An ordinary invalid syntax position returns None rather than a guess. -/
def Tree.redexCursors {g : Net signature N B W} (tree : Tree g) (p : Path) :
    Option (Cursor g .app × Cursor g .lam) :=
  match tree.nodeAt p with
  | some (.app appCursor (.lam lambdaCursor _) _) => some (appCursor,lambdaCursor)
  | _ => none

omit [DecidableEq N] [DecidableEq B] [DecidableEq W] in
theorem Tree.redexCursors_complete {g : Net signature N B W} (tree : Tree g)
    (p : Path) (redex : ∃ t,subtermAt tree.erase p=some t ∧ IsRedex t) :
    ∃ app lam,tree.redexCursors p=some (app,lam) := by
  have erased := tree.nodeAt_erase p
  cases located : tree.nodeAt p with
  | none =>
    obtain ⟨t,atTerm,_valid⟩ := redex
    rw [located,atTerm] at erased
    cases erased
  | some sub =>
    have atSub : subtermAt tree.erase p=some sub.erase := by
      simpa only [located,Option.map_some] using erased.symm
    obtain ⟨t,atTerm,valid⟩ := redex
    have same : sub.erase=t := Option.some.inj (atSub.symm.trans atTerm)
    have validSub : IsRedex sub.erase := same.symm ▸ valid
    cases sub with
    | var cursor index => simp only [Tree.erase,IsRedex] at validSub
    | lam cursor body => simp only [Tree.erase,IsRedex] at validSub
    | app appCursor function argument =>
      cases function with
      | var cursor index => simp only [Tree.erase,IsRedex] at validSub
      | app cursor left right => simp only [Tree.erase,IsRedex] at validSub
      | lam lambdaCursor body =>
        exact ⟨appCursor,lambdaCursor,by simp only [Tree.redexCursors,located]⟩

inductive Task (g : Net signature N B W) where
  | read (departure : Endpoint g) (context : ContextData)
      (stem : List (Endpoint g)) (frames : List (BinderFrame g))
  | buildApp (cursor : Cursor g .app)
  | buildLam (cursor : Cursor g .lam)

def Task.erase {g : Net signature N B W} : Task g → ReadbackTask g
  | .read d a stem frames => .read d a stem frames
  | .buildApp _ => .buildApp
  | .buildLam _ => .buildLam

structure State (g : Net signature N B W) where
  pending : List (Task g)
  values : List (Tree g)

def State.erase {g : Net signature N B W} (state : State g) : MachineState g :=
  ⟨state.pending.map Task.erase,state.values.map Tree.erase⟩

inductive Result (g : Net signature N B W) where
  | next (state : State g)
  | done (tree : Tree g)
  | failed (reason : MachineFailure)

def Result.erase {g : Net signature N B W} : Result g → MachineStep g
  | .next state => .next state.erase
  | .done tree => .done tree.erase
  | .failed reason => .failed reason

private def portAt (g : Net signature N B W) (node : N) (op : Op)
    (sort : (g.label node).sort=.op op) (port : Port (.op op)) : Endpoint g :=
  .inl ⟨node,sort.symm ▸ port⟩

/-- Same actual traversal and binding test as P10; saved build cursors are
the only extra data. No Matches, source term, or semantic selection is read. -/
def step (g : Net signature N B W) (state : State g) : Result g :=
  match state.pending with
  | [] => match state.values with
      | [tree] => .done tree
      | _ => .failed .malformedStack
  | .buildApp cursor::rest => match state.values with
      | argument::function::values => .next ⟨rest,.app cursor function argument::values⟩
      | _ => .failed .malformedStack
  | .buildLam cursor::rest => match state.values with
      | body::values => .next ⟨rest,.lam cursor body::values⟩
      | _ => .failed .malformedStack
  | .read departure context stem frames::rest =>
    match scan : scanOne g departure context with
    | .failed reason => .failed (.scan reason)
    | .next next after =>
      .next ⟨.read next after (stem++[departure]) frames::rest,state.values⟩
    | .terminal arrival kind after =>
      let path := stem++[departure]
      match kind with
      | .app =>
        if sort : (g.label arrival.1).sort=.op .app then
          let cursor : Cursor g .app := ⟨departure,context,stem,frames,arrival,after,scan⟩
          let function := portAt g arrival.1 .app sort (.inl ())
          let argument := portAt g arrival.1 .app sort appArg
          .next ⟨.read function after path frames::
            .read argument after path frames::.buildApp cursor::rest,state.values⟩
        else .failed .inconsistentTerminal
      | .lam =>
        if sort : (g.label arrival.1).sort=.op .lam then
          let cursor : Cursor g .lam := ⟨departure,context,stem,frames,arrival,after,scan⟩
          let body := portAt g arrival.1 .lam sort lamBody
          let frame : BinderFrame g := ⟨arrival.1,(g.label arrival.1).index,path,body,after⟩
          .next ⟨.read body after path (frame::frames)::.buildLam cursor::rest,state.values⟩
        else .failed .inconsistentTerminal
      | .var => match binderCandidates g frames arrival.1 path after with
          | [index] =>
            let cursor : Cursor g .var := ⟨departure,context,stem,frames,arrival,after,scan⟩
            .next ⟨rest,.var cursor index::state.values⟩
          | [] => .failed .missingBinder
          | _ => .failed .ambiguousBinder

theorem step_erase (g : Net signature N B W) (state : State g) :
    (step g state).erase = machineStep g state.erase := by
  rcases state with ⟨pending,values⟩
  cases pending with
  | nil =>
    cases values with
    | nil => rfl
    | cons tree values => cases values <;> rfl
  | cons task rest =>
    cases task with
    | buildApp cursor =>
      cases values with
      | nil => rfl
      | cons argument values => cases values <;> rfl
    | buildLam cursor => cases values <;> rfl
    | read departure context stem frames =>
      -- Split the actual dependent match itself. Rewriting scanOne by simp
      -- cannot transport its equation proof stored in every terminal Cursor.
      simp only [step]
      split
      next reason scanned =>
        simp only [Result.erase,State.erase,List.map_cons,Task.erase,machineStep,scanned]
      next nextDeparture nextContext scanned =>
        simp only [Result.erase,State.erase,List.map_cons,Task.erase,machineStep,scanned]
      next arrival kind after scanned =>
        cases kind with
        | app =>
          -- This split is still the indexed (kind,scan) matcher, not the if.
          split
          · by_cases sort : (g.label arrival.1).sort=.op .app
            · simp only [Result.erase,State.erase,List.map_cons,Task.erase,machineStep,scanned,dif_pos sort]
              rfl
            · simp only [Result.erase,State.erase,List.map_cons,Task.erase,machineStep,scanned,dif_neg sort]
          · contradiction
          · contradiction
        | lam =>
          split
          · contradiction
          · by_cases sort : (g.label arrival.1).sort=.op .lam
            · simp only [Result.erase,State.erase,List.map_cons,Task.erase,machineStep,scanned,dif_pos sort]
              rfl
            · simp only [Result.erase,State.erase,List.map_cons,Task.erase,machineStep,scanned,dif_neg sort]
          · contradiction
        | var =>
          cases candidates : binderCandidates g frames arrival.1 (stem++[departure]) after with
          | nil =>
            simp only [Result.erase,State.erase,List.map_cons,Task.erase,machineStep,scanned,candidates]
          | cons index indices =>
            cases indices with
            | nil =>
              simp only [Result.erase,State.erase,List.map_cons,Task.erase,Tree.erase,machineStep,scanned,candidates]
            | cons nextIndex more =>
              simp only [Result.erase,State.erase,List.map_cons,Task.erase,machineStep,scanned,candidates]

def initial (g : Net signature N B W) (root : B) : State g :=
  ⟨[.read (.inr (.inl root)) [] [] []],[]⟩

omit [DecidableEq N] [DecidableEq B] [DecidableEq W] in
theorem initial_erase (g : Net signature N B W) (root : B) :
    (initial g root).erase = initialState g root := rfl

inductive Run (g : Net signature N B W) where
  | exhausted (state : State g)
  | done (tree : Tree g)
  | failed (reason : MachineFailure)

def Run.erase {g : Net signature N B W} : Run g → MachineRun g
  | .exhausted state => .exhausted state.erase
  | .done tree => .done tree.erase
  | .failed reason => .failed reason

def fuel (g : Net signature N B W) : Nat → State g → Run g
  | 0,state => .exhausted state
  | n+1,state => match step g state with
      | .next next => fuel g n next
      | .done tree => .done tree
      | .failed reason => .failed reason

theorem fuel_erase (g : Net signature N B W) (n : Nat) (state : State g) :
    (fuel g n state).erase = machineFuel g n state.erase := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
    cases actual : step g state with
    | next next =>
      have old : machineStep g state.erase=.next next.erase := by
        simpa only [actual,Result.erase] using (step_erase g state).symm
      simpa only [fuel,actual,Run.erase,machineFuel,old] using ih next
    | done tree =>
      have old : machineStep g state.erase=.done tree.erase := by
        simpa only [actual,Result.erase] using (step_erase g state).symm
      simp only [fuel,actual,Run.erase,machineFuel,old]
    | failed reason =>
      have old : machineStep g state.erase=.failed reason := by
        simpa only [actual,Result.erase] using (step_erase g state).symm
      simp only [fuel,actual,Run.erase,machineFuel,old]

/-- A successful enriched output is the original successful output. -/
theorem fuel_done_original {g : Net signature N B W} {n : Nat} {state : State g}
    {tree : Tree g} (done : fuel g n state=.done tree) :
    machineFuel g n state.erase=.done tree.erase := by
  simpa only [done,Run.erase] using (fuel_erase g n state).symm

/-- Reuse the original P10 accessibility proposition on the erased state.
The old machine's domain proof is not a cursor or output oracle. -/
def AccessibleState (g : Net signature N B W) :=
  {state : State g // Acc (MachineNext g) state.erase}

private instance (g : Net signature N B W) : WellFoundedRelation (AccessibleState g) where
  rel := InvImage (MachineNext g) (fun state => state.val.erase)
  wf := ⟨fun state => InvImage.accessible (fun s : AccessibleState g => s.val.erase)
    state.property⟩

/-- Unbounded annotated execution using only the original erased-state domain.
Failure remains an explicit None, exactly as in the P10 effective wrapper. -/
def runOnAccessible (g : Net signature N B W) (state : AccessibleState g) :
    Option (Tree g) :=
  match actual : step g state.val with
  | .next next =>
    have old : MachineNext g next.erase state.val.erase := by
      change machineStep g state.val.erase=.next next.erase
      simpa only [actual,Result.erase] using (step_erase g state.val).symm
    runOnAccessible g ⟨next,state.property.inv old⟩
  | .done tree => some tree
  | .failed _ => none
termination_by state
decreasing_by exact old

#print axioms Lamping.AG.Readback.OccurrenceData.Cursor
#print axioms Lamping.AG.Readback.OccurrenceData.Cursor.path
#print axioms Lamping.AG.Readback.OccurrenceData.Tree
#print axioms Lamping.AG.Readback.OccurrenceData.Tree.erase
#print axioms Lamping.AG.Readback.OccurrenceData.Tree.nodeAt
#print axioms Lamping.AG.Readback.OccurrenceData.Tree.cursorAt
#print axioms Lamping.AG.Readback.OccurrenceData.Tree.nodeAt_erase
#print axioms Lamping.AG.Readback.OccurrenceData.Tree.cursorAt_some
#print axioms Lamping.AG.Readback.OccurrenceData.Tree.redexCursors
#print axioms Lamping.AG.Readback.OccurrenceData.Tree.redexCursors_complete
#print axioms Lamping.AG.Readback.OccurrenceData.step
#print axioms Lamping.AG.Readback.OccurrenceData.step_erase
#print axioms Lamping.AG.Readback.OccurrenceData.initial
#print axioms Lamping.AG.Readback.OccurrenceData.initial_erase
#print axioms Lamping.AG.Readback.OccurrenceData.fuel
#print axioms Lamping.AG.Readback.OccurrenceData.fuel_erase
#print axioms Lamping.AG.Readback.OccurrenceData.fuel_done_original
#print axioms Lamping.AG.Readback.OccurrenceData.AccessibleState
#print axioms Lamping.AG.Readback.OccurrenceData.runOnAccessible

end
end Lamping.AG.Readback.OccurrenceData
