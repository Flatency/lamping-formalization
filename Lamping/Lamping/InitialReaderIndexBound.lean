import Lamping.Lamping.RootInitialControlStep

namespace Lamping.AG
open Graph Lambda

private theorem readerIndex_label (actual : Graph.Label signature) (op : Op)
    (sort : actual.sort=.op op) : actual=label op actual.index := by
  cases actual
  cases sort
  rfl

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {depths : B → Int} {root : B}

/-- Expose the strict inequality already enforced on the actual initial
reader by root-input variation. No choice of rewrite or full I is needed. -/
theorem ActualRedexAccess.initial_reader_index_lt {t : Term} {redex : RedexOcc t}
    (access : ActualRedexAccess g root redex) (inputs : RootInputs g root)
    (balance : IndexedLevelBalance g depths) (rootDepth : depths root=0)
    (route : TransparentCorridor g)
    (rightPrincipal : IsPrincipal (g:=g) route.last)
    (rightControl : IsControlNode (g:=g) route.last.1)
    (next : Endpoint g) (remaining : List (Endpoint g))
    (split : access.connection.edges=route.edges++next::remaining) :
    (g.label route.last.1).index<access.connection.appIndex := by
  obtain ⟨op,sort,control⟩ := rightControl
  obtain ⟨other,otherSort,principal⟩ := rightPrincipal
  have same : other=op := Kind.op.inj (otherSort.symm.trans sort)
  subst other
  have rightLabel := readerIndex_label (g.label route.last.1) op sort
  by_cases lower : (g.label route.last.1).index<access.connection.appIndex
  · exact lower
  · obtain ⟨input,seam,parentLabels⟩ := access.parent.property.1.1
    let index := (g.label route.last.1).index
    let width := access.connection.appIndex
    have high : width≤index := by omega
    let chosen := Context.empty.replace (index-width) (Context.empty.cons (controlRejectingLevel op))
    have bad : (seam.replace width chosen).get index=controlRejectingLevel op := by
      rw [Context.replace_high _ _ high]
      change (Context.empty.replace (index-width) (Context.empty.cons (controlRejectingLevel op))).get
        (index-width)=_
      simp only [Context.replace_high _ _ (Nat.le_refl _),Nat.sub_self,Context.cons_zero]
    obtain ⟨output,changed⟩ := access.connection_tail_inputs inputs balance rootDepth parentLabels chosen
    have whole : Labelling g (route.edges++next::remaining) (seam.replace width chosen) output := by
      rw [←split]
      exact changed
    have readerLabels := whole.corridor_initial_seam route (next::remaining)
    cases readerLabels with
    | cons turn rest =>
      rw [Pairing.involutive] at turn
      obtain ⟨outgoing,leaves,_rule⟩ := turn.from_node route.last.1 route.last.2 rfl
      obtain ⟨before,routeSplit⟩ := List.getLast?_eq_some_iff.mp route.finish
      let entry := g.wire (Sum.inl route.last)
      have exactWhole : Labelling g (before++entry::next::remaining)
          (seam.replace width chosen) output := by
        simpa only [routeSplit,List.append_assoc,List.singleton_append] using whole
      have transparent : ∀ x y,(x,y)∈(before++[entry]).zip (before++[entry]).tail →
          ∃ w d,g.wire x=Sum.inr (Sum.inr (w,d)) ∧ y=Sum.inr (Sum.inr (w,!d)) := by
        simpa only [routeSplit] using route.transparent
      exact False.elim (exactWhole.no_rejected_control_prefix before entry next remaining transparent
        route.last.1 route.last.2 outgoing op index rightLabel control principal
        (Pairing.involutive _ _) leaves bad)
end
end Lamping.AG
