import Lamping.Lamping.ReadbackUnboundedCursorInterface
import Lamping.Lamping.MatchingRedexEndpointUniqueness

namespace Lamping.AG.Readback.OccurrenceData
open Graph Lambda

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

theorem Tree.nodeAt_append (tree : Tree g) (p q : Path) :
    tree.nodeAt (p++q)=(tree.nodeAt p).bind (fun sub => sub.nodeAt q) := by
  induction p generalizing tree with
  | nil => cases tree <;> rfl
  | cons direction p ih =>
    cases tree <;> cases direction <;>
      simp only [List.cons_append,Tree.nodeAt,Option.bind_none,ih]

theorem Tree.redexCursors_cursorAt {tree : Tree g} {p : Path}
    {app : Cursor g .app} {lam : Cursor g .lam}
    (query : tree.redexCursors p=some (app,lam)) :
    tree.cursorAt p=some ⟨.app,app⟩ ∧ tree.cursorAt (p++[.fn])=some ⟨.lam,lam⟩ := by
  cases atNode : tree.nodeAt p with
  | none => simp [Tree.redexCursors,atNode] at query
  | some sub =>
    cases sub with
    | var cursor index => simp [Tree.redexCursors,atNode] at query
    | lam cursor body => simp [Tree.redexCursors,atNode] at query
    | app saved function argument =>
      cases function with
      | var cursor index => simp [Tree.redexCursors,atNode] at query
      | app cursor left right => simp [Tree.redexCursors,atNode] at query
      | lam binder body =>
        have same : (saved,binder)=(app,lam) := Option.some.inj (by
          simpa only [Tree.redexCursors,atNode] using query)
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
        constructor
        · simp only [Tree.cursorAt,atNode,Option.map_some,Tree.cursor]
        · rw [Tree.cursorAt,Tree.nodeAt_append,atNode]
          rfl

namespace ActualRedexCursor

/-- Literal physical data only, with no semantic witness or chosen list. -/
def suffix (app : Cursor g .app) (lam : Cursor g .lam) : List (Endpoint g) :=
  lam.path.drop app.path.length

private theorem cursor_last {kind : AccessKind} (cursor : Cursor g kind) :
    cursor.path.getLast?=some cursor.departure := by
  simp only [Cursor.path,List.getLast?_append,List.getLast?_singleton,Option.some_or]

private theorem cursor_node_of_finish {root : B} {kind : AccessKind}
    (cursor : Cursor g kind) (access : RootAccess g root) (samePath : access.val=cursor.path)
    (node : N) (port : Port (g.label node).sort)
    (finish : access.val.getLast?=some (g.wire (.inl ⟨node,port⟩))) :
    node=cursor.arrival.1 := by
  have last : cursor.path.getLast?=some (g.wire (.inl ⟨node,port⟩)) := by
    rw [←samePath]; exact finish
  have departure : cursor.departure=g.wire (.inl ⟨node,port⟩) :=
    Option.some.inj ((cursor_last cursor).symm.trans last)
  have wired : g.wire cursor.departure=.inl ⟨node,port⟩ := by
    rw [departure,Pairing.involutive]
  have terminal := scanOne_terminal_sound g cursor.departure cursor.arrival kind
    cursor.input cursor.output cursor.actual
  have same : (.inl cursor.arrival : Endpoint g)=.inl ⟨node,port⟩ :=
    terminal.1.symm.trans wired
  exact (congrArg Sigma.fst (Sum.inl.inj same)).symm

section Execution
variable [DecidableEq N] [DecidableEq B] [DecidableEq W]

def parentAccess {root : B} {tree : Tree g}
    (accessible : Acc (MachineNext g) (initial g root).erase)
    (success : runOnAccessible g ⟨initial g root,accessible⟩=some tree)
    {p : Path} {app : Cursor g .app} {lam : Cursor g .lam}
    (query : tree.redexCursors p=some (app,lam)) : RootAccess g root :=
  Unbounded.initial_success_cursor_access accessible success
    (Tree.redexCursors_cursorAt query).1

def childAccess {root : B} {tree : Tree g}
    (accessible : Acc (MachineNext g) (initial g root).erase)
    (success : runOnAccessible g ⟨initial g root,accessible⟩=some tree)
    {p : Path} {app : Cursor g .app} {lam : Cursor g .lam}
    (query : tree.redexCursors p=some (app,lam)) : RootAccess g root :=
  Unbounded.initial_success_cursor_access accessible success
    (Tree.redexCursors_cursorAt query).2

theorem access_paths {root : B} {tree : Tree g}
    (accessible : Acc (MachineNext g) (initial g root).erase)
    (success : runOnAccessible g ⟨initial g root,accessible⟩=some tree)
    {p : Path} {app : Cursor g .app} {lam : Cursor g .lam}
    (query : tree.redexCursors p=some (app,lam)) :
    (parentAccess accessible success query).val=app.path ∧
      (childAccess accessible success query).val=lam.path := ⟨rfl,rfl⟩

theorem access_words {root : B} {tree : Tree g}
    (accessible : Acc (MachineNext g) (initial g root).erase)
    (success : runOnAccessible g ⟨initial g root,accessible⟩=some tree)
    {p : Path} {app : Cursor g .app} {lam : Cursor g .lam}
    (query : tree.redexCursors p=some (app,lam)) :
    accessWord g app.path=p ∧ accessWord g lam.path=p++[.fn] := by
  exact ⟨Unbounded.initial_success_cursor_word accessible success
      (Tree.redexCursors_cursorAt query).1,
    Unbounded.initial_success_cursor_word accessible success
      (Tree.redexCursors_cursorAt query).2⟩

/-- The semantic witness is used only inside this proposition, to prove that
our already fixed paths and drop suffix are the actual redex geometry. -/
theorem semantic_identification {root : B} {tree : Tree g}
    (accessible : Acc (MachineNext g) (initial g root).erase)
    (success : runOnAccessible g ⟨initial g root,accessible⟩=some tree)
    (matching : Matches g root tree.erase) (redex : RedexOcc tree.erase)
    {app : Cursor g .app} {lam : Cursor g .lam}
    (query : tree.redexCursors redex.val=some (app,lam)) :
    ∃ actual : ActualRedexAccess g root redex,
      actual.parent.val=app.path ∧ actual.child.val=lam.path ∧
      actual.connection.app=app.arrival.1 ∧ actual.connection.lam=lam.arrival.1 ∧
      actual.connection.edges=suffix app lam := by
  obtain ⟨actual⟩ := matching.actual_redex_access redex
  let parent := parentAccess accessible success query
  let child := childAccess accessible success query
  have words := access_words accessible success query
  have parentSame : parent=actual.parent := matching.accessWord_injective
    (words.1.trans actual.parentWord.symm)
  have childSame : child=actual.child := matching.accessWord_injective
    (words.2.trans actual.childWord.symm)
  have parentPath : actual.parent.val=app.path := by
    rw [←parentSame]; rfl
  have childPath : actual.child.val=lam.path := by
    rw [←childSame]; rfl
  have appNode := cursor_node_of_finish app actual.parent parentPath
    actual.connection.app actual.ctx actual.parentFinish
  have childFinish : actual.child.val.getLast?=
      some (g.wire (.inl ⟨actual.connection.lam,actual.connection.lamPort⟩)) := by
    rw [actual.split,List.getLast?_append,actual.connection.finish]
    rfl
  have lamNode := cursor_node_of_finish lam actual.child childPath
    actual.connection.lam actual.connection.lamPort childFinish
  have split : lam.path=app.path++actual.connection.edges := by
    rw [←childPath,actual.split,parentPath]
  have dropped := congrArg (List.drop app.path.length) split
  have suffixEq : actual.connection.edges=suffix app lam := by
    symm
    simpa only [suffix,List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append]
      using dropped
  exact ⟨actual,parentPath,childPath,appNode,lamNode,suffixEq⟩

theorem suffix_geometry {root : B} {tree : Tree g}
    (accessible : Acc (MachineNext g) (initial g root).erase)
    (success : runOnAccessible g ⟨initial g root,accessible⟩=some tree)
    (matching : Matches g root tree.erase) (redex : RedexOcc tree.erase)
    {app : Cursor g .app} {lam : Cursor g .lam}
    (query : tree.redexCursors redex.val=some (app,lam)) :
    ForwardProperPath g (suffix app lam) ∧ lam.path=app.path++suffix app lam := by
  obtain ⟨actual,parentPath,childPath,_appNode,_lamNode,sameSuffix⟩ :=
    semantic_identification accessible success matching redex query
  constructor
  · rw [←sameSuffix]; exact actual.connection.proper
  · rw [←childPath,actual.split,parentPath,sameSuffix]

end Execution
end ActualRedexCursor

#print axioms Lamping.AG.Readback.OccurrenceData.Tree.nodeAt_append
#print axioms Lamping.AG.Readback.OccurrenceData.Tree.redexCursors_cursorAt
#print axioms Lamping.AG.Readback.OccurrenceData.ActualRedexCursor.suffix
#print axioms Lamping.AG.Readback.OccurrenceData.ActualRedexCursor.parentAccess
#print axioms Lamping.AG.Readback.OccurrenceData.ActualRedexCursor.childAccess
#print axioms Lamping.AG.Readback.OccurrenceData.ActualRedexCursor.access_paths
#print axioms Lamping.AG.Readback.OccurrenceData.ActualRedexCursor.access_words
#print axioms Lamping.AG.Readback.OccurrenceData.ActualRedexCursor.semantic_identification
#print axioms Lamping.AG.Readback.OccurrenceData.ActualRedexCursor.suffix_geometry

end
end Lamping.AG.Readback.OccurrenceData
