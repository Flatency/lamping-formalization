import Lamping.Lamping.ControlCorridorEndpoints
import Lamping.Lamping.CorridorBoundaryTurns
import Lamping.Lamping.BalancedControlTerminal
namespace Lamping.AG
open Graph

private theorem label_from_sort (actual : Label signature) (op : Op) (sort : actual.sort=.op op) :
    actual=label op actual.index := by cases actual; cases sort; rfl

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {directions : B → Bool} {depths : B → Int} {root : B}

/-- Final control/lambda case. Actual indexed balance supplies the terminal
tail synchronization that excludes high writers. Lambda context is used only
as an incoming terminal, never as an outgoing source. -/
theorem RedexConnection.terminal_control_graph_step (connection : RedexConnection g)
    (balance : IndexedLevelBalance g depths) (rootDepth : depths root=0)
    (flow : FlowBalance g directions) (route : TransparentCorridor g)
    (last : route.last=⟨connection.lam,connection.lamPort⟩)
    (leftPrincipal : IsPrincipal (g:=g) route.first)
    (leftControl : IsControlNode (g:=g) route.first.1)
    (before : List (Endpoint g)) (nonempty : before≠[])
    (split : connection.edges=before++route.edges) :
    ∃ schema target,GraphStep schema (ActualNet.ofNet g) target := by
  obtain ⟨op,sort,control⟩ := leftControl
  obtain ⟨other,otherSort,principal⟩ := leftPrincipal
  have same : other=op := Kind.op.inj (otherSort.symm.trans sort)
  subst other
  have leftLabel := label_from_sort (g.label route.first.1) op sort
  by_cases lower : (g.label route.first.1).index<connection.lamIndex
  · exact low_control_corridor_graph_step control lower flow route route.first.1 connection.lam
      leftLabel connection.lamLabel route.first.2 connection.lamPort principal connection.lamPrincipal
      rfl last
  · obtain ⟨a,b,original⟩ := connection.proper.1
    have whole : Labelling g ((before++route.edges)++[]) a b := by
      simpa only [List.append_nil,←split] using original
    obtain ⟨middle,leftBoundary,_rightBoundary⟩ := whole.corridor_boundary_turns route before []
    rcases leftBoundary with ⟨empty,_same⟩ |⟨initial,previous,input,beforeSplit,_prefix,writer⟩
    · exact False.elim (nonempty empty)
    · obtain ⟨incoming,arrives,_reverseRule⟩ := writer.reverse.from_node route.first.1 route.first.2 rfl
      obtain ⟨rest,routeSplit⟩ := List.head?_eq_some_iff.mp route.start
      have actualSplit : connection.edges=initial++previous::(.inl route.first)::rest := by
        simpa only [beforeSplit,routeSplit,List.append_assoc,List.singleton_append] using split
      have labels : Labelling g (initial++previous::(.inl route.first)::rest) a b := by
        rw [←actualSplit]; exact original
      have forward : Forward g (initial++previous::(.inl route.first)::rest) := by
        rw [←actualSplit]; exact connection.proper.2
      have start : (initial++previous::(.inl route.first)::rest).head?=
          some (.inl ⟨connection.app,connection.appPort⟩) := actualSplit ▸ connection.start
      have finish : (initial++previous::(.inl route.first)::rest).getLast?=
          some (g.wire (.inl ⟨connection.lam,connection.lamPort⟩)) := actualSplit ▸ connection.finish
      have transparent : ∀ x y,(x,y)∈((.inl route.first)::rest).zip ((.inl route.first)::rest).tail →
          ∃ w d,g.wire x=.inr (.inr (w,d)) ∧y=.inr (.inr (w,!d)) := by
        simpa only [routeSplit] using route.transparent
      exact False.elim (balance.no_high_control_terminal rootDepth initial previous (.inl route.first) rest
        (.inl ⟨connection.app,connection.appPort⟩) (.inl ⟨connection.lam,connection.lamPort⟩)
        .appFun .lamCtx connection.appIndex connection.lamIndex a b start finish
        (.appFun connection.app connection.appPort connection.appIndex connection.appLabel connection.appPrincipal)
        trivial
        (.lamCtx connection.lam connection.lamPort connection.lamIndex connection.lamLabel connection.lamPrincipal)
        trivial forward labels transparent route.first.1 incoming route.first.2 op (g.label route.first.1).index
        leftLabel control principal arrives rfl (by simpa only [ProperRole.terminalWidth] using Nat.le_of_not_gt lower))
end
end Lamping.AG
