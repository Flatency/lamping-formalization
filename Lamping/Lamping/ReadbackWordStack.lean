import Lamping.Lamping.ReadbackCursorScheduling

namespace Lamping.AG.Readback.OccurrenceData.WordStack
open Graph Lambda

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

def rootWord : Tree g → Path
  | .var cursor _ => accessWord g cursor.path
  | .app cursor _ _ => accessWord g cursor.path
  | .lam cursor _ => accessWord g cursor.path

def TreeWords : Tree g → Prop
  | .var _ _ => True
  | .app cursor function argument =>
      TreeWords function ∧ TreeWords argument ∧
        rootWord function=accessWord g cursor.path++[.fn] ∧
        rootWord argument=accessWord g cursor.path++[.arg]
  | .lam cursor body => TreeWords body ∧ rootWord body=accessWord g cursor.path++[.body]

def readWord (departure : Endpoint g) (stem : List (Endpoint g)) : Path :=
  accessWord g (stem++[departure])

/-- Static consumption of the ENTIRE remaining task/value stack. It is a
proof target initialized from the machine, never a field of any task or cursor. -/
inductive StackFlow (g : Net signature N B W) : List (Task g) → List Path → Path → Prop where
  | done (word) : StackFlow g [] [word] word
  | read {departure context stem frames rest words final}
      (tail : StackFlow g rest (readWord departure stem::words) final) :
      StackFlow g (.read departure context stem frames::rest) words final
  | app {cursor rest words final}
      (tail : StackFlow g rest (accessWord g cursor.path::words) final) :
      StackFlow g (.buildApp cursor::rest)
        ((accessWord g cursor.path++[.arg])::(accessWord g cursor.path++[.fn])::words) final
  | lam {cursor rest words final}
      (tail : StackFlow g rest (accessWord g cursor.path::words) final) :
      StackFlow g (.buildLam cursor::rest) ((accessWord g cursor.path++[.body])::words) final

def Invariant (final : Path) (state : State g) : Prop :=
  (∀ tree,tree∈state.values → TreeWords tree) ∧
    StackFlow g state.pending (state.values.map rootWord) final

theorem initial_invariant (root : B) : Invariant [] (initial g root) := by
  refine ⟨?_,StackFlow.read (StackFlow.done [])⟩
  intro tree member
  cases member

theorem StackFlow.read_inv {departure context stem frames rest words final}
    (flow : StackFlow g (.read departure context stem frames::rest) words final) :
    StackFlow g rest (readWord departure stem::words) final := by
  cases flow with
  | read tail => exact tail

theorem StackFlow.app_inv {cursor rest words final}
    (flow : StackFlow g (.buildApp cursor::rest) words final) :
    ∃ tailWords,words=(accessWord g cursor.path++[.arg])::
      (accessWord g cursor.path++[.fn])::tailWords ∧
      StackFlow g rest (accessWord g cursor.path::tailWords) final := by
  cases flow with
  | app tail => exact ⟨_,rfl,tail⟩

theorem StackFlow.lam_inv {cursor rest words final}
    (flow : StackFlow g (.buildLam cursor::rest) words final) :
    ∃ tailWords,words=(accessWord g cursor.path++[.body])::tailWords ∧
      StackFlow g rest (accessWord g cursor.path::tailWords) final := by
  cases flow with
  | lam tail => exact ⟨_,rfl,tail⟩

theorem StackFlow.nil_inv {words final} (flow : StackFlow g [] words final) :
    words=[final] := by
  cases flow
  rfl

private theorem rootWord_cursor (tree : Tree g) :
    rootWord tree=accessWord g tree.cursor.2.path := by cases tree <;> rfl

theorem TreeWords.node_word {tree : Tree g} (good : TreeWords tree) {p : Path} {sub : Tree g}
    (located : tree.nodeAt p=some sub) : rootWord sub=rootWord tree++p := by
  induction p generalizing tree with
  | nil =>
    have atRoot : tree.nodeAt []=some tree := by cases tree <;> rfl
    have same : tree=sub := Option.some.inj (atRoot.symm.trans located)
    cases same
    exact (List.append_nil _).symm
  | cons direction p ih =>
    cases tree with
    | var cursor index => cases direction <;> simp [Tree.nodeAt] at located
    | app cursor function argument =>
      cases direction with
      | body => simp [Tree.nodeAt] at located
      | fn =>
        change rootWord sub=accessWord g cursor.path++(.fn::p)
        calc
          rootWord sub = rootWord function++p := ih (tree:=function) good.1 located
          _ = (accessWord g cursor.path++[.fn])++p := by rw [good.2.2.1]
          _ = _ := by simp only [List.append_assoc,List.singleton_append]
      | arg =>
        change rootWord sub=accessWord g cursor.path++(.arg::p)
        calc
          rootWord sub = rootWord argument++p := ih (tree:=argument) good.2.1 located
          _ = (accessWord g cursor.path++[.arg])++p := by rw [good.2.2.2]
          _ = _ := by simp only [List.append_assoc,List.singleton_append]
    | lam cursor body =>
      cases direction with
      | fn => simp [Tree.nodeAt] at located
      | arg => simp [Tree.nodeAt] at located
      | body =>
        change rootWord sub=accessWord g cursor.path++(.body::p)
        calc
          rootWord sub = rootWord body++p := ih (tree:=body) good.1 located
          _ = (accessWord g cursor.path++[.body])++p := by rw [good.2]
          _ = _ := by simp only [List.append_assoc,List.singleton_append]

/-- An eliminator for the INTERNAL terminal proof state. The theorem that
all complete initial executions reach this invariant is still a separate goal. -/
theorem Invariant.terminal_cursor_word {final : Path} {tree : Tree g}
    (inv : Invariant final (⟨[],[tree]⟩ : State g)) {p : Path}
    {cursor : Sigma (Cursor g)} (located : tree.cursorAt p=some cursor) :
    accessWord g cursor.2.path=final++p := by
  have good : TreeWords tree := inv.1 tree (by simp)
  have words := StackFlow.nil_inv inv.2
  have eqList : [rootWord tree]=[final] := by
    simpa only [List.map_cons,List.map_nil] using words
  have root : rootWord tree=final := (List.cons.inj eqList).1
  obtain ⟨sub,atSub,same,_syntax⟩ := Tree.cursorAt_some located
  have position := good.node_word atSub
  rw [root] at position
  have physical : rootWord sub=accessWord g cursor.2.path := by
    rw [rootWord_cursor,same]
  exact physical.symm.trans position

private def token : (kind : Kind) → Port kind → Path
  | .op .app,.inl () => [.fn]
  | .op .app,.inr true => [.arg]
  | .op .lam,.inr true => [.body]
  | _,_ => []

private theorem control_token {i : Nat} {kind : Kind} {p q : Port kind}
    {a b : ContextData} (actual : executeControl i kind p a=some (q,b)) : token kind q=[] := by
  cases kind with
  | garbage => simp [executeControl] at actual
  | op op =>
    cases op with
    | app => simp [executeControl] at actual
    | lam => simp [executeControl] at actual
    | fan => cases q <;> rfl
    | cro => cases q <;> rfl
    | bra => cases q <;> rfl

theorem scan_next_empty_token {e f : Endpoint g} {a b : ContextData}
    (actual : scanOne g e a=.next f b) : arrivalWord g f=[] := by
  cases wire : g.wire e with
  | inl arrival =>
    rcases arrival with ⟨node,port⟩
    cases role : portKind (g.label node).sort port with
    | some kind => simp [scanOne,wire,role] at actual
    | none =>
      cases turn : executeControl (g.label node).index (g.label node).sort port a with
      | none => simp [scanOne,wire,role,turn] at actual
      | some result =>
        rcases result with ⟨out,after⟩
        simp only [scanOne,wire,role,turn,ScanResult.next.injEq] at actual
        obtain ⟨rfl,rfl⟩ := actual
        change token (g.label node).sort out=[]
        exact control_token turn
  | inr target =>
    cases target with
    | inl boundary => simp [scanOne,wire] at actual
    | inr wireNode =>
      rcases wireNode with ⟨vertex,direction⟩
      simp only [scanOne,wire,ScanResult.next.injEq] at actual
      obtain ⟨rfl,rfl⟩ := actual
      rfl

theorem read_word_after_next {e f : Endpoint g} {a b : ContextData}
    (actual : scanOne g e a=.next f b) (stem : List (Endpoint g)) :
    readWord f (stem++[e])=readWord e stem := by
  unfold readWord
  rw [accessWord_append g _ _ (by simp)]
  simp only [List.flatMap_cons,List.flatMap_nil,scan_next_empty_token actual,List.append_nil]

section Execution
variable [DecidableEq N] [DecidableEq B] [DecidableEq W]

/-- This consumes the WHOLE pending/value IH. The two child words are
derived by inversion of StackFlow, not supplied as desired equalities. -/
theorem Invariant.build_app {final : Path} (cursor : Cursor g .app)
    (function argument : Tree g) (rest : List (Task g)) (values : List (Tree g))
    (inv : Invariant final ⟨.buildApp cursor::rest,argument::function::values⟩) :
    step g ⟨.buildApp cursor::rest,argument::function::values⟩=
      .next ⟨rest,.app cursor function argument::values⟩ ∧
      Invariant final ⟨rest,.app cursor function argument::values⟩ := by
  refine ⟨rfl,?_⟩
  rcases inv with ⟨all,flow⟩
  obtain ⟨tailWords,equal,tail⟩ := StackFlow.app_inv flow
  have eqList : rootWord argument::rootWord function::values.map rootWord=
      (accessWord g cursor.path++[.arg])::(accessWord g cursor.path++[.fn])::tailWords := by
    simpa only [List.map_cons] using equal
  obtain ⟨argumentWord,restEq⟩ := List.cons.inj eqList
  obtain ⟨functionWord,tailEq⟩ := List.cons.inj restEq
  have good : TreeWords (.app cursor function argument) :=
    ⟨all function (by simp),all argument (by simp),functionWord,argumentWord⟩
  refine ⟨?_,?_⟩
  · intro tree member
    rcases List.mem_cons.mp member with same | remaining
    · cases same
      exact good
    · exact all tree (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr remaining))))
  · change StackFlow g rest (rootWord (.app cursor function argument)::values.map rootWord) final
    rw [rootWord,tailEq]
    exact tail

theorem Invariant.build_lam {final : Path} (cursor : Cursor g .lam)
    (body : Tree g) (rest : List (Task g)) (values : List (Tree g))
    (inv : Invariant final ⟨.buildLam cursor::rest,body::values⟩) :
    step g ⟨.buildLam cursor::rest,body::values⟩=.next ⟨rest,.lam cursor body::values⟩ ∧
      Invariant final ⟨rest,.lam cursor body::values⟩ := by
  refine ⟨rfl,?_⟩
  rcases inv with ⟨all,flow⟩
  obtain ⟨tailWords,equal,tail⟩ := StackFlow.lam_inv flow
  have eqList : rootWord body::values.map rootWord=(accessWord g cursor.path++[.body])::tailWords := by
    simpa only [List.map_cons] using equal
  obtain ⟨bodyWord,tailEq⟩ := List.cons.inj eqList
  have good : TreeWords (.lam cursor body) := ⟨all body (by simp),bodyWord⟩
  refine ⟨?_,?_⟩
  · intro tree member
    rcases List.mem_cons.mp member with same | remaining
    · cases same
      exact good
    · exact all tree (List.mem_cons.mpr (Or.inr remaining))
  · change StackFlow g rest (rootWord (.lam cursor body)::values.map rootWord) final
    rw [rootWord,tailEq]
    exact tail

private theorem one_step {before after : State g} (trace : Steps g 1 before after) :
    step g before=.next after := by
  cases trace with
  | cons actual tail =>
    cases tail with
    | refl => exact actual

theorem Invariant.scan_next {final : Path} {e f : Endpoint g} {a b : ContextData}
    (actual : scanOne g e a=.next f b) (stem : List (Endpoint g))
    (frames : List (BinderFrame g)) (rest : List (Task g)) (values : List (Tree g))
    (inv : Invariant final ⟨.read e a stem frames::rest,values⟩) :
    step g ⟨.read e a stem frames::rest,values⟩=
        .next ⟨.read f b (stem++[e]) frames::rest,values⟩ ∧
      Invariant final ⟨.read f b (stem++[e]) frames::rest,values⟩ := by
  let trace : ScanSteps g 1 e a f b := .cons actual (.refl f b)
  have first := one_step (scan_advances trace stem frames rest values)
  refine ⟨?_,inv.1,?_⟩
  · simpa only [trace,ScanSteps.departures] using first
  · apply StackFlow.read
    rw [read_word_after_next actual]
    exact StackFlow.read_inv inv.2

end Execution

#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.rootWord
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.TreeWords
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.readWord
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.StackFlow
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.Invariant
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.initial_invariant
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.StackFlow.read_inv
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.StackFlow.app_inv
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.StackFlow.lam_inv
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.StackFlow.nil_inv
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.TreeWords.node_word
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.Invariant.terminal_cursor_word
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.scan_next_empty_token
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.read_word_after_next
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.Invariant.build_app
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.Invariant.build_lam
#print axioms Lamping.AG.Readback.OccurrenceData.WordStack.Invariant.scan_next

end
end Lamping.AG.Readback.OccurrenceData.WordStack
