import Lamping.Lamping.ControlCorridorEndpoints
import Lamping.Lamping.CorridorOccurrenceSeams
import Lamping.Lamping.ControlInitialObstruction
namespace Lamping.AG
open Graph

private theorem label_from_sort (actual : Label signature) (op : Op) (sort : actual.sort=.op op) :
    actual=label op actual.index := by cases actual; cases sort; rfl

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {directions : B → Bool} {root : B}

/-- Initial app/control case of a given complete redex connection. A reader
at or above the application index is rejected using whole-path Independence;
a lower reader supplies the actual action on the reversed corridor. -/
theorem RedexConnection.initial_control_graph_step (connection : RedexConnection g)
    (independence : Independence g root) (flow : FlowBalance g directions)
    (route : TransparentCorridor g)
    (first : route.first=⟨connection.app,connection.appPort⟩)
    (rightPrincipal : IsPrincipal (g:=g) route.last)
    (rightControl : IsControlNode (g:=g) route.last.1)
    (next : Endpoint g) (remaining : List (Endpoint g))
    (split : connection.edges=route.edges++next::remaining) :
    ∃ schema target,GraphStep schema (ActualNet.ofNet g) target := by
  obtain ⟨op,sort,control⟩ := rightControl
  obtain ⟨other,otherSort,principal⟩ := rightPrincipal
  have same : other=op := Kind.op.inj (otherSort.symm.trans sort)
  subst other
  have rightLabel := label_from_sort (g.label route.last.1) op sort
  by_cases lower : (g.label route.last.1).index<connection.appIndex
  · exact low_control_corridor_graph_step control lower flow route.reverse route.last.1 connection.app
      rightLabel connection.appLabel route.last.2 connection.appPort principal connection.appPrincipal
      rfl first
  · obtain ⟨a,b,original⟩ := connection.proper.1
    have whole : Labelling g (route.edges++next::remaining) a b := by rw [←split]; exact original
    have readerLabels := whole.corridor_initial_seam route (next::remaining)
    cases readerLabels with
    | cons turn rest =>
      rw [Pairing.involutive] at turn
      obtain ⟨outgoing,leaves,_rule⟩ := turn.from_node route.last.1 route.last.2 rfl
      obtain ⟨before,routeSplit⟩ := List.getLast?_eq_some_iff.mp route.finish
      let entry := g.wire (.inl route.last)
      have actualSplit : connection.edges=before++entry::next::remaining := by
        simpa only [routeSplit,List.append_assoc,List.singleton_append] using split
      have labels : Labelling g (before++entry::next::remaining) a b := by rw [←actualSplit]; exact original
      have forward : Forward g (before++entry::next::remaining) := by rw [←actualSplit]; exact connection.proper.2
      have start : (before++entry::next::remaining).head?=
          some (.inl ⟨connection.app,connection.appPort⟩) := actualSplit ▸ connection.start
      have finish : (before++entry::next::remaining).getLast?=
          some (g.wire (.inl ⟨connection.lam,connection.lamPort⟩)) := actualSplit ▸ connection.finish
      have transparent : ∀ x y,(x,y)∈(before++[entry]).zip (before++[entry]).tail →
          ∃ w d,g.wire x=.inr (.inr (w,d)) ∧y=.inr (.inr (w,!d)) := by
        simpa only [routeSplit] using route.transparent
      exact False.elim (independence.no_high_control_initial before entry next remaining
        (.inl ⟨connection.app,connection.appPort⟩) (.inl ⟨connection.lam,connection.lamPort⟩)
        .appFun .lamCtx connection.appIndex connection.lamIndex a b start finish
        (.appFun connection.app connection.appPort connection.appIndex connection.appLabel connection.appPrincipal)
        trivial
        (.lamCtx connection.lam connection.lamPort connection.lamIndex connection.lamLabel connection.lamPrincipal)
        trivial forward labels transparent route.last.1 route.last.2 outgoing op (g.label route.last.1).index
        rightLabel control principal (Pairing.involutive _ _) leaves (by omega))
end
end Lamping.AG
