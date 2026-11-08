import Lamping.Lamping.RedexRootInputs
import Lamping.Lamping.InitialControlCorridorStep
namespace Lamping.AG
open Graph Lambda

private theorem label_from_sort (actual : Label signature) (op : Op) (sort : actual.sort=.op op) :
    actual=label op actual.index := by cases actual; cases sort; rfl

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {depths : B → Int} {directions : B → Bool} {root : B}

/-- Initial control case using the actual parent/child root accesses, not
arbitrary proper-source Independence. The high marker is realized on the
same whole child path with its parent low shell retained. -/
theorem ActualRedexAccess.root_initial_control_graph_step {t : Term} {redex : RedexOcc t}
    (access : ActualRedexAccess g root redex) (inputs : RootInputs g root)
    (balance : IndexedLevelBalance g depths) (rootDepth : depths root=0)
    (flow : FlowBalance g directions) (route : TransparentCorridor g)
    (first : route.first=⟨access.connection.app,access.connection.appPort⟩)
    (rightPrincipal : IsPrincipal (g:=g) route.last)
    (rightControl : IsControlNode (g:=g) route.last.1)
    (next : Endpoint g) (remaining : List (Endpoint g))
    (split : access.connection.edges=route.edges++next::remaining) :
    ∃ schema target,GraphStep schema (ActualNet.ofNet g) target := by
  obtain ⟨op,sort,control⟩ := rightControl
  obtain ⟨other,otherSort,principal⟩ := rightPrincipal
  have same : other=op := Kind.op.inj (otherSort.symm.trans sort)
  subst other
  have rightLabel := label_from_sort (g.label route.last.1) op sort
  by_cases lower : (g.label route.last.1).index<access.connection.appIndex
  · exact low_control_corridor_graph_step control lower flow route.reverse route.last.1 access.connection.app
      rightLabel access.connection.appLabel route.last.2 access.connection.appPort
      principal access.connection.appPrincipal rfl first
  · obtain ⟨input,seam,parentLabels⟩ := access.parent.property.1.1
    let index := (g.label route.last.1).index
    let width := access.connection.appIndex
    have high : width≤index := by omega
    let chosen := Context.empty.replace (index-width) (Context.empty.cons (controlRejectingLevel op))
    have bad : (seam.replace width chosen).get index=controlRejectingLevel op := by
      rw [Context.replace_high _ _ high]
      change (Context.empty.replace (index-width) (Context.empty.cons (controlRejectingLevel op))).get (index-width)=_
      simp only [Context.replace_high _ _ (Nat.le_refl _),Nat.sub_self,Context.cons_zero]
    obtain ⟨output,changed⟩ := access.connection_tail_inputs inputs balance rootDepth parentLabels chosen
    have whole : Labelling g (route.edges++next::remaining) (seam.replace width chosen) output := by
      rw [←split]; exact changed
    have readerLabels := whole.corridor_initial_seam route (next::remaining)
    cases readerLabels with
    | cons turn rest =>
      rw [Pairing.involutive] at turn
      obtain ⟨outgoing,leaves,_rule⟩ := turn.from_node route.last.1 route.last.2 rfl
      obtain ⟨before,routeSplit⟩ := List.getLast?_eq_some_iff.mp route.finish
      let entry := g.wire (.inl route.last)
      have exactWhole : Labelling g (before++entry::next::remaining) (seam.replace width chosen) output := by
        simpa only [routeSplit,List.append_assoc,List.singleton_append] using whole
      have transparent : ∀ x y,(x,y)∈(before++[entry]).zip (before++[entry]).tail →
          ∃ w d,g.wire x=.inr (.inr (w,d)) ∧y=.inr (.inr (w,!d)) := by
        simpa only [routeSplit] using route.transparent
      exact False.elim (exactWhole.no_rejected_control_prefix before entry next remaining transparent
        route.last.1 route.last.2 outgoing op index rightLabel control principal
        (Pairing.involutive _ _) leaves bad)
end
end Lamping.AG
