import Lamping.Lamping.ReadbackCursorSemantics
import Lamping.Lamping.InitialAccessWords

namespace Lamping.AG.Readback.OccurrenceData
open Graph Lambda

private instance signatureKindEquality : DecidableEq signature.Kind :=
  inferInstanceAs (DecidableEq Kind)

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable [DecidableEq N] [DecidableEq B] [DecidableEq W]
variable {g : Net signature N B W}

def functionDeparture (cursor : Cursor g .app)
    (sort : (g.label cursor.arrival.1).sort=.op .app) : Endpoint g :=
  .inl ⟨cursor.arrival.1,sort.symm ▸ (Sum.inl () : Port (.op .app))⟩

def argumentDeparture (cursor : Cursor g .app)
    (sort : (g.label cursor.arrival.1).sort=.op .app) : Endpoint g :=
  .inl ⟨cursor.arrival.1,sort.symm ▸ appArg⟩

def bodyDeparture (cursor : Cursor g .lam)
    (sort : (g.label cursor.arrival.1).sort=.op .lam) : Endpoint g :=
  .inl ⟨cursor.arrival.1,sort.symm ▸ lamBody⟩

def pushedFrame (cursor : Cursor g .lam)
    (sort : (g.label cursor.arrival.1).sort=.op .lam) : BinderFrame g :=
  ⟨cursor.arrival.1,(g.label cursor.arrival.1).index,cursor.path,
    bodyDeparture cursor sort,cursor.output⟩

def appAfter (cursor : Cursor g .app)
    (sort : (g.label cursor.arrival.1).sort=.op .app)
    (rest : List (Task g)) (values : List (Tree g)) : State g :=
  ⟨.read (functionDeparture cursor sort) cursor.output cursor.path cursor.frames::
    .read (argumentDeparture cursor sort) cursor.output cursor.path cursor.frames::
    .buildApp cursor::rest,values⟩

def lamAfter (cursor : Cursor g .lam)
    (sort : (g.label cursor.arrival.1).sort=.op .lam)
    (rest : List (Task g)) (values : List (Tree g)) : State g :=
  ⟨.read (bodyDeparture cursor sort) cursor.output cursor.path
      (pushedFrame cursor sort::cursor.frames)::.buildLam cursor::rest,values⟩

/-- The actual terminal match supplies the saved builder cursor and both
child tasks; no preservation law or semantic decoder is a premise. -/
theorem app_schedules (cursor : Cursor g .app)
    (sort : (g.label cursor.arrival.1).sort=.op .app)
    (rest : List (Task g)) (values : List (Tree g)) :
    step g ⟨.read cursor.departure cursor.input cursor.stem cursor.frames::rest,values⟩=
      .next (appAfter cursor sort rest values) := by
  rcases cursor with ⟨departure,input,stem,frames,arrival,output,actual⟩
  simp only [step]
  split
  next reason scanned => cases actual.symm.trans scanned
  next nextDeparture nextContext scanned => cases actual.symm.trans scanned
  next otherArrival otherKind otherOutput scanned =>
    obtain ⟨rfl,rfl,rfl⟩ := ScanResult.terminal.inj (actual.symm.trans scanned)
    -- Dispose mismatched kind/scan branches before reducing the real guard.
    -- If the indexed match has already reduced, this also handles its if.
    split <;> first
    | contradiction
    | (simp only [appAfter,functionDeparture,argumentDeparture,Cursor.path] <;>
        first | rfl | (rw [dif_pos sort] <;> rfl))

theorem lam_schedules (cursor : Cursor g .lam)
    (sort : (g.label cursor.arrival.1).sort=.op .lam)
    (rest : List (Task g)) (values : List (Tree g)) :
    step g ⟨.read cursor.departure cursor.input cursor.stem cursor.frames::rest,values⟩=
      .next (lamAfter cursor sort rest values) := by
  rcases cursor with ⟨departure,input,stem,frames,arrival,output,actual⟩
  simp only [step]
  split
  next reason scanned => cases actual.symm.trans scanned
  next nextDeparture nextContext scanned => cases actual.symm.trans scanned
  next otherArrival otherKind otherOutput scanned =>
    obtain ⟨rfl,rfl,rfl⟩ := ScanResult.terminal.inj (actual.symm.trans scanned)
    -- Dispose mismatched kind/scan branches before reducing the real guard.
    -- If the indexed match has already reduced, this also handles its if.
    split <;> first
    | contradiction
    | (simp only [lamAfter,pushedFrame,bodyDeparture,Cursor.path] <;>
        first | rfl | (rw [dif_pos sort] <;> rfl))

private def departureToken : (kind : Kind) → Port kind → Path
  | .op .app,.inl () => [.fn]
  | .op .app,.inr true => [.arg]
  | .op .lam,.inr true => [.body]
  | _,_ => []

private theorem app_tokens {kind : Kind} (sort : kind=.op .app) :
    departureToken kind (sort.symm ▸ (Sum.inl () : Port (.op .app)))=[.fn] ∧
      departureToken kind (sort.symm ▸ appArg)=[.arg] := by
  subst kind
  exact ⟨rfl,rfl⟩

private theorem body_token {kind : Kind} (sort : kind=.op .lam) :
    departureToken kind (sort.symm ▸ lamBody)=[.body] := by
  subst kind
  rfl

/- Both actual APP child read paths have the original parent's literal
stem and exactly the correct new syntax edge. No word equality is assumed. -/
omit [DecidableEq N] [DecidableEq B] [DecidableEq W] in
theorem app_child_words (cursor : Cursor g .app)
    (sort : (g.label cursor.arrival.1).sort=.op .app) :
    accessWord g (cursor.path++[functionDeparture cursor sort])=
        accessWord g cursor.path++[.fn] ∧
      accessWord g (cursor.path++[argumentDeparture cursor sort])=
        accessWord g cursor.path++[.arg] := by
  have nonempty : cursor.path≠[] := by simp [Cursor.path]
  have fnWord : arrivalWord g (functionDeparture cursor sort)=[.fn] := by
    change departureToken (g.label cursor.arrival.1).sort
      (sort.symm ▸ (Sum.inl () : Port (.op .app)))=[.fn]
    exact (app_tokens sort).1
  have argWord : arrivalWord g (argumentDeparture cursor sort)=[.arg] := by
    change departureToken (g.label cursor.arrival.1).sort (sort.symm ▸ appArg)=[.arg]
    exact (app_tokens sort).2
  constructor
  · rw [accessWord_append g _ _ nonempty]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,fnWord]
  · rw [accessWord_append g _ _ nonempty]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,argWord]

omit [DecidableEq N] [DecidableEq B] [DecidableEq W] in
theorem lam_child_word (cursor : Cursor g .lam)
    (sort : (g.label cursor.arrival.1).sort=.op .lam) :
    accessWord g (cursor.path++[bodyDeparture cursor sort])=
      accessWord g cursor.path++[.body] := by
  have nonempty : cursor.path≠[] := by simp [Cursor.path]
  have bodyWord : arrivalWord g (bodyDeparture cursor sort)=[.body] := by
    change departureToken (g.label cursor.arrival.1).sort (sort.symm ▸ lamBody)=[.body]
    exact body_token sort
  rw [accessWord_append g _ _ nonempty]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,bodyWord]

private theorem steps_snoc {n : Nat} {before middle after : State g}
    (prior : Steps g n before middle) (last : step g middle=.next after) :
    Steps g (n+1) before after := by
  induction prior with
  | refl => exact .cons last (.refl _)
  | cons first _tail ih => exact .cons first (ih last)

theorem initial_app_scheduling {root : B} {n : Nat} {last : Endpoint g}
    {context output : ContextData} {arrival : NodePort signature N g.label}
    (trace : ScanSteps g n (.inr (.inl root)) [] last context)
    (terminal : scanOne g last context=.terminal arrival .app output)
    (sort : (g.label arrival.1).sort=.op .app) :
    Steps g (n+1) (initial g root) (appAfter (rootScanCursor trace terminal) sort [] []) ∧
      accessWord g ((rootScanCursor trace terminal).path++
        [functionDeparture (rootScanCursor trace terminal) sort])=
          accessWord g (rootScanCursor trace terminal).path++[.fn] ∧
      accessWord g ((rootScanCursor trace terminal).path++
        [argumentDeparture (rootScanCursor trace terminal) sort])=
          accessWord g (rootScanCursor trace terminal).path++[.arg] := by
  refine ⟨steps_snoc (initial_scan_steps trace) ?_,app_child_words _ _⟩
  exact app_schedules (rootScanCursor trace terminal) sort [] []

theorem initial_lam_scheduling {root : B} {n : Nat} {last : Endpoint g}
    {context output : ContextData} {arrival : NodePort signature N g.label}
    (trace : ScanSteps g n (.inr (.inl root)) [] last context)
    (terminal : scanOne g last context=.terminal arrival .lam output)
    (sort : (g.label arrival.1).sort=.op .lam) :
    Steps g (n+1) (initial g root) (lamAfter (rootScanCursor trace terminal) sort [] []) ∧
      accessWord g ((rootScanCursor trace terminal).path++
        [bodyDeparture (rootScanCursor trace terminal) sort])=
          accessWord g (rootScanCursor trace terminal).path++[.body] := by
  refine ⟨steps_snoc (initial_scan_steps trace) ?_,lam_child_word _ _⟩
  exact lam_schedules (rootScanCursor trace terminal) sort [] []

/-- The actual build consumes argument before function, but places them at
their correct syntax positions and retains the SAME saved APP cursor. -/
theorem build_app_positions (cursor : Cursor g .app) (function argument : Tree g)
    (rest : List (Task g)) (values : List (Tree g)) :
    step g ⟨.buildApp cursor::rest,argument::function::values⟩=
      .next ⟨rest,.app cursor function argument::values⟩ ∧
      (Tree.app cursor function argument).cursorAt []=some ⟨.app,cursor⟩ ∧
      (∀ p,(Tree.app cursor function argument).cursorAt (.fn::p)=function.cursorAt p ∧
        (Tree.app cursor function argument).cursorAt (.arg::p)=argument.cursorAt p) := by
  refine ⟨rfl,rfl,?_⟩
  intro p
  exact ⟨rfl,rfl⟩

theorem build_lam_positions (cursor : Cursor g .lam) (body : Tree g)
    (rest : List (Task g)) (values : List (Tree g)) :
    step g ⟨.buildLam cursor::rest,body::values⟩=.next ⟨rest,.lam cursor body::values⟩ ∧
      (Tree.lam cursor body).cursorAt []=some ⟨.lam,cursor⟩ ∧
      (∀ p,(Tree.lam cursor body).cursorAt (.body::p)=body.cursorAt p) :=
  ⟨rfl,rfl,fun _ => rfl⟩

#print axioms Lamping.AG.Readback.OccurrenceData.functionDeparture
#print axioms Lamping.AG.Readback.OccurrenceData.argumentDeparture
#print axioms Lamping.AG.Readback.OccurrenceData.bodyDeparture
#print axioms Lamping.AG.Readback.OccurrenceData.pushedFrame
#print axioms Lamping.AG.Readback.OccurrenceData.appAfter
#print axioms Lamping.AG.Readback.OccurrenceData.lamAfter
#print axioms Lamping.AG.Readback.OccurrenceData.app_schedules
#print axioms Lamping.AG.Readback.OccurrenceData.lam_schedules
#print axioms Lamping.AG.Readback.OccurrenceData.app_child_words
#print axioms Lamping.AG.Readback.OccurrenceData.lam_child_word
#print axioms Lamping.AG.Readback.OccurrenceData.initial_app_scheduling
#print axioms Lamping.AG.Readback.OccurrenceData.initial_lam_scheduling
#print axioms Lamping.AG.Readback.OccurrenceData.build_app_positions
#print axioms Lamping.AG.Readback.OccurrenceData.build_lam_positions

end
end Lamping.AG.Readback.OccurrenceData
