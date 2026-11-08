import Lamping.Lamping.ReadbackActualRedexCursor

namespace Lamping.AG.Readback.OccurrenceData.ActualRedexCursor
open Graph Lambda

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

private theorem snd_heq {α : Type} {β : α → Type} {x y : Sigma β} (same : x=y) :
    HEq x.2 y.2 := by cases same; rfl

private theorem nodeport_eq {first second : N} {p : Port (g.label first).sort}
    {q : Port (g.label second).sort} (nodes : first=second) (ports : HEq p q) :
    (⟨first,p⟩ : NodePort signature N g.label)=⟨second,q⟩ := by
  cases nodes
  cases eq_of_heq ports
  rfl

private theorem cast_role {kind target : Kind} (sort : kind=target) (port : Port target) :
    HEq (sort.symm ▸ port) port := by subst target; rfl

private theorem label_of_sort (actual : Label signature) (op : Op)
    (sort : actual.sort=.op op) : actual=label op actual.index := by
  cases actual with
  | mk kind index => cases sort; rfl

private theorem arrival_eq_of_finish {root : B} {kind : AccessKind}
    (cursor : Cursor g kind) (access : RootAccess g root) (path : access.val=cursor.path)
    (node : N) (port : Port (g.label node).sort)
    (finish : access.val.getLast?=some (g.wire (.inl ⟨node,port⟩))) :
    (⟨node,port⟩ : NodePort signature N g.label)=cursor.arrival := by
  have last : cursor.path.getLast?=some cursor.departure := by
    simp only [Cursor.path,List.getLast?_append,List.getLast?_singleton,Option.some_or]
  have endEq : cursor.departure=g.wire (.inl ⟨node,port⟩) := by
    apply Option.some.inj
    rw [←last,←path]
    exact finish
  have wire : g.wire cursor.departure=.inl ⟨node,port⟩ := by
    rw [endEq,Pairing.involutive]
  have actual := scanOne_terminal_sound g cursor.departure cursor.arrival kind
    cursor.input cursor.output cursor.actual
  exact Sum.inl.inj (wire.symm.trans actual.1)

/-- Internal fixed-data proof target. It is derived below, not a public caller
parameter and not a field read by the evaluator or cursor query. -/
private structure FixedFacts (app : Cursor g .app) (lam : Cursor g .lam) : Prop where
  appSort : (g.label app.arrival.1).sort=.op .app
  lamSort : (g.label lam.arrival.1).sort=.op .lam
  contextRole : HEq app.arrival.2 appCtx
  lambdaRole : HEq lam.arrival.2 (Sum.inl () : Port (.op .lam))
  proper : ForwardProperPath g (suffix app lam)
  start : (suffix app lam).head?=some (functionDeparture app appSort)
  finish : (suffix app lam).getLast?=some (g.wire (.inl lam.arrival))
  emptyWord : accessWord g (suffix app lam)=[]
  parentFinish : app.path.getLast?=some (g.wire (.inl app.arrival))
  split : lam.path=app.path++suffix app lam

section Execution
variable [DecidableEq N] [DecidableEq B] [DecidableEq W]

private theorem fixed_facts {root : B} {tree : Tree g}
    (accessible : Acc (MachineNext g) (initial g root).erase)
    (success : runOnAccessible g ⟨initial g root,accessible⟩=some tree)
    (matching : Matches g root tree.erase) (redex : RedexOcc tree.erase)
    {app : Cursor g .app} {lam : Cursor g .lam}
    (query : tree.redexCursors redex.val=some (app,lam)) : FixedFacts app lam := by
  obtain ⟨actual,parentPath,childPath,appNode,lamNode,edgeEq⟩ :=
    semantic_identification accessible success matching redex query
  have childFinish : actual.child.val.getLast?=
      some (g.wire (.inl ⟨actual.connection.lam,actual.connection.lamPort⟩)) := by
    rw [actual.split,List.getLast?_append,actual.connection.finish]
    rfl
  have sameContext := arrival_eq_of_finish app actual.parent parentPath
    actual.connection.app actual.ctx actual.parentFinish
  have sameLambda := arrival_eq_of_finish lam actual.child childPath
    actual.connection.lam actual.connection.lamPort childFinish
  have appSort : (g.label app.arrival.1).sort=.op .app := by
    rw [←appNode,actual.connection.appLabel]; rfl
  have lamSort : (g.label lam.arrival.1).sort=.op .lam := by
    rw [←lamNode,actual.connection.lamLabel]; rfl
  have principal : (.inl ⟨actual.connection.app,actual.connection.appPort⟩ : Endpoint g)=
      functionDeparture app appSort := by
    apply congrArg (fun p : NodePort signature N g.label => (Sum.inl p : Endpoint g))
    exact nodeport_eq appNode
      (actual.connection.appPrincipal.trans (cast_role appSort (Sum.inl () : Port (.op .app))).symm)
  refine {
    appSort := appSort
    lamSort := lamSort
    contextRole := (snd_heq sameContext).symm.trans actual.contextPrincipal
    lambdaRole := (snd_heq sameLambda).symm.trans actual.connection.lamPrincipal
    proper := ?_
    start := ?_
    finish := ?_
    emptyWord := ?_
    parentFinish := ?_
    split := ?_
  }
  · rw [←edgeEq]; exact actual.connection.proper
  · rw [←edgeEq,actual.connection.start,principal]
  · rw [←edgeEq,actual.connection.finish,sameLambda]
  · rw [←edgeEq]; exact actual.connection.emptyWord
  · rw [←parentPath,actual.parentFinish,sameContext]
  · rw [←childPath,actual.split,parentPath,edgeEq]

/-- Fixed physical data for the actual computed syntax redex. The semantic
witness is eliminated only while proving fixed_facts; no witness is returned. -/
def actualAccess {root : B} {tree : Tree g}
    (accessible : Acc (MachineNext g) (initial g root).erase)
    (success : runOnAccessible g ⟨initial g root,accessible⟩=some tree)
    (matching : Matches g root tree.erase) (redex : RedexOcc tree.erase)
    {app : Cursor g .app} {lam : Cursor g .lam}
    (query : tree.redexCursors redex.val=some (app,lam)) : ActualRedexAccess g root redex :=
  let facts := fixed_facts accessible success matching redex query
  { connection := {
      app:=app.arrival.1,lam:=lam.arrival.1,
      appPort:=facts.appSort.symm ▸ (Sum.inl () : Port (.op .app)),
      lamPort:=lam.arrival.2,
      appIndex:=(g.label app.arrival.1).index,lamIndex:=(g.label lam.arrival.1).index,
      appLabel:=label_of_sort _ .app facts.appSort,lamLabel:=label_of_sort _ .lam facts.lamSort,
      appPrincipal:=cast_role facts.appSort (Sum.inl () : Port (.op .app)),
      lamPrincipal:=facts.lambdaRole,
      edges:=suffix app lam,proper:=facts.proper,
      start:=facts.start,finish:=facts.finish,emptyWord:=facts.emptyWord },
    parent:=parentAccess accessible success query,child:=childAccess accessible success query,
    ctx:=app.arrival.2,contextPrincipal:=facts.contextRole,
    parentWord:=(access_words accessible success query).1,
    childWord:=(access_words accessible success query).2,
    parentFinish:=facts.parentFinish,split:=facts.split }

theorem actualAccess_data {root : B} {tree : Tree g}
    (accessible : Acc (MachineNext g) (initial g root).erase)
    (success : runOnAccessible g ⟨initial g root,accessible⟩=some tree)
    (matching : Matches g root tree.erase) (redex : RedexOcc tree.erase)
    {app : Cursor g .app} {lam : Cursor g .lam}
    (query : tree.redexCursors redex.val=some (app,lam)) :
    (actualAccess accessible success matching redex query).parent.val=app.path ∧
    (actualAccess accessible success matching redex query).child.val=lam.path ∧
    (actualAccess accessible success matching redex query).connection.edges=lam.path.drop app.path.length ∧
    (actualAccess accessible success matching redex query).connection.app=app.arrival.1 ∧
    (actualAccess accessible success matching redex query).connection.lam=lam.arrival.1 ∧
    (actualAccess accessible success matching redex query).connection.appIndex=(g.label app.arrival.1).index ∧
    (actualAccess accessible success matching redex query).connection.lamIndex=(g.label lam.arrival.1).index :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end Execution

#print axioms Lamping.AG.Readback.OccurrenceData.ActualRedexCursor.actualAccess
#print axioms Lamping.AG.Readback.OccurrenceData.ActualRedexCursor.actualAccess_data

end
end Lamping.AG.Readback.OccurrenceData.ActualRedexCursor
