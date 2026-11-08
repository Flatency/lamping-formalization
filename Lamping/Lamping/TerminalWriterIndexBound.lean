import Lamping.Lamping.TerminalControlCorridorStep

namespace Lamping.AG
open Graph

private theorem terminalIndex_label (actual : Graph.Label signature) (op : Op)
    (sort : actual.sort=.op op) : actual=label op actual.index := by
  cases actual
  cases sort
  rfl

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {depths : B → Int} {root : B}

/-- An actual terminal writer has lower index than THIS connection's lambda.
The high case contradicts indexed terminal synchronization on the full path. -/
theorem RedexConnection.terminal_writer_index_lt (connection : RedexConnection g)
    (balance : IndexedLevelBalance g depths) (rootDepth : depths root=0)
    (route : TransparentCorridor g)
    (leftPrincipal : IsPrincipal (g:=g) route.first)
    (leftControl : IsControlNode (g:=g) route.first.1)
    (before : List (Endpoint g)) (nonempty : before≠[])
    (split : connection.edges=before++route.edges) :
    (g.label route.first.1).index<connection.lamIndex := by
  obtain ⟨op,sort,control⟩ := leftControl
  obtain ⟨other,otherSort,principal⟩ := leftPrincipal
  have same : other=op := Kind.op.inj (otherSort.symm.trans sort)
  subst other
  have leftLabel := terminalIndex_label (g.label route.first.1) op sort
  by_cases lower : (g.label route.first.1).index<connection.lamIndex
  · exact lower
  · obtain ⟨a,b,original⟩ := connection.proper.1
    have whole : Labelling g ((before++route.edges)++[]) a b := by
      simpa only [List.append_nil,←split] using original
    obtain ⟨middle,leftBoundary,_rightBoundary⟩ := whole.corridor_boundary_turns route before []
    rcases leftBoundary with ⟨empty,_same⟩ |⟨initial,previous,input,beforeSplit,_pref,writer⟩
    · exact False.elim (nonempty empty)
    · obtain ⟨incoming,arrives,_reverseRule⟩ := writer.reverse.from_node route.first.1 route.first.2 rfl
      obtain ⟨rest,routeSplit⟩ := List.head?_eq_some_iff.mp route.start
      have actualSplit : connection.edges=initial++previous::(Sum.inl route.first)::rest := by
        simpa only [beforeSplit,routeSplit,List.append_assoc,List.singleton_append] using split
      have labels : Labelling g (initial++previous::(Sum.inl route.first)::rest) a b := by
        rw [←actualSplit]
        exact original
      have forward : Forward g (initial++previous::(Sum.inl route.first)::rest) := by
        rw [←actualSplit]
        exact connection.proper.2
      have start : (initial++previous::(Sum.inl route.first)::rest).head?=
          some (Sum.inl ⟨connection.app,connection.appPort⟩) := actualSplit ▸ connection.start
      have finish : (initial++previous::(Sum.inl route.first)::rest).getLast?=
          some (g.wire (Sum.inl ⟨connection.lam,connection.lamPort⟩)) := actualSplit ▸ connection.finish
      have transparent : ∀ x y,(x,y)∈((Sum.inl route.first)::rest).zip ((Sum.inl route.first)::rest).tail →
          ∃ w d,g.wire x=Sum.inr (Sum.inr (w,d)) ∧ y=Sum.inr (Sum.inr (w,!d)) := by
        simpa only [routeSplit] using route.transparent
      exact False.elim (balance.no_high_control_terminal rootDepth initial previous (Sum.inl route.first) rest
        (Sum.inl ⟨connection.app,connection.appPort⟩) (Sum.inl ⟨connection.lam,connection.lamPort⟩)
        .appFun .lamCtx connection.appIndex connection.lamIndex a b start finish
        (.appFun connection.app connection.appPort connection.appIndex connection.appLabel connection.appPrincipal)
        trivial
        (.lamCtx connection.lam connection.lamPort connection.lamIndex connection.lamLabel connection.lamPrincipal)
        trivial forward labels transparent route.first.1 incoming route.first.2 op (g.label route.first.1).index
        leftLabel control principal arrives rfl (by simpa only [ProperRole.terminalWidth] using Nat.le_of_not_gt lower))
end
end Lamping.AG
