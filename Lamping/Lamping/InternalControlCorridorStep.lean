import Lamping.Lamping.ControlCorridorEndpoints
import Lamping.Lamping.CorridorBoundaryTurns
namespace Lamping.AG
open Graph

private theorem label_from_sort (actual : Label signature) (op : Op) (sort : actual.sort=.op op) :
    actual=label op actual.index := by cases actual; cases sort; rfl

private theorem writer_rule (actual : Label signature) (op : Op)
    (p q : Port actual.sort) (sort : actual.sort=.op op)
    (principal : HEq q (Sum.inl () : Port (.op op)))
    {a b : Context} (rule : Traversal actual.index actual.sort p q a b) :
    ∃ incoming : Port (.op op),Traversal actual.index (.op op) incoming (.inl ()) a b := by
  cases actual with
  | mk kind index =>
    cases sort
    have same : q=.inl () := eq_of_heq principal
    subst q
    exact ⟨p,rule⟩

private theorem reader_rule (actual : Label signature) (op : Op)
    (p q : Port actual.sort) (sort : actual.sort=.op op)
    (principal : HEq p (Sum.inl () : Port (.op op)))
    {a b : Context} (rule : Traversal actual.index actual.sort p q a b) :
    ∃ outgoing : Port (.op op),Traversal actual.index (.op op) (.inl ()) outgoing a b := by
  cases actual with
  | mk kind index =>
    cases sort
    have same : p=.inl () := eq_of_heq principal
    subst p
    exact ⟨q,rule⟩

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {boundary : B → Bool}

/-- Two actual boundary turns on the same seam supply marker compatibility
for the existing control corridor. All labels and schema metadata are derived
from the actual endpoint nodes. -/
theorem control_corridor_step_of_boundary_turns
    (flow : FlowBalance g boundary) (route : TransparentCorridor g)
    (leftPrincipal : IsPrincipal (g:=g) route.first)
    (rightPrincipal : IsPrincipal (g:=g) route.last)
    (leftControl : IsControlNode (g:=g) route.first.1)
    (rightControl : IsControlNode (g:=g) route.last.1)
    (previous next : Endpoint g) {a middle b : Context}
    (writer : LabelledTurn g (g.wire previous) (.inl route.first) a middle)
    (reader : LabelledTurn g (.inl route.last) next middle b) :
    ∃ schema target,GraphStep schema (ActualNet.ofNet g) target := by
  obtain ⟨left,ls,lc⟩ := leftControl
  obtain ⟨right,rs,rc⟩ := rightControl
  obtain ⟨lop,ls',lp⟩ := leftPrincipal
  obtain ⟨rop,rs',rp⟩ := rightPrincipal
  have sameLeft : lop=left := Kind.op.inj (ls'.symm.trans ls)
  have sameRight : rop=right := Kind.op.inj (rs'.symm.trans rs)
  subst lop
  subst rop
  obtain ⟨incoming,_arrival,reverseRule⟩ := writer.reverse.from_node route.first.1 route.first.2 rfl
  obtain ⟨outgoing,_leaves,rule⟩ := reader.from_node route.last.1 route.last.2 rfl
  obtain ⟨actualIn,leftRule⟩ := writer_rule _ left incoming route.first.2 ls lp reverseRule.reverse
  obtain ⟨actualOut,rightRule⟩ := reader_rule _ right route.last.2 outgoing rs rp rule
  exact control_corridor_graph_step lc rc leftRule rightRule flow route route.first.1 route.last.1
    (label_from_sort _ left ls) (label_from_sort _ right rs) route.first.2 route.last.2 lp rp rfl rfl

/-- Every wholly internal principal corridor occurrence of a supplied
control/W labelled path produces an actual rewrite. Both outside pieces are
nonempty, so its real boundary turns are control writer and reader. -/
theorem Labelling.internal_control_corridor_step {es : List (Endpoint g)} {a b : Context}
    (labels : Labelling g es a b)
    (only : ∀ e f,(e,f)∈es.zip es.tail →ControlOnlyTurn (g:=g) e f)
    (flow : FlowBalance g boundary) (route : TransparentCorridor g)
    (leftPrincipal : IsPrincipal (g:=g) route.first)
    (rightPrincipal : IsPrincipal (g:=g) route.last)
    (before after : List (Endpoint g)) (split : es=(before++route.edges)++after)
    (leftNonempty : before≠[]) (rightNonempty : after≠[]) :
    ∃ schema target,GraphStep schema (ActualNet.ofNet g) target := by
  have leftControl := control_corridor_left only route before after split leftNonempty
  have rightControl := control_corridor_right only route before after split rightNonempty
  have whole : Labelling g ((before++route.edges)++after) a b := by rw [←split]; exact labels
  obtain ⟨middle,leftBoundary,rightBoundary⟩ := whole.corridor_boundary_turns route before after
  rcases leftBoundary with ⟨empty,_same⟩ |⟨initial,previous,input,_before,_pref,writer⟩
  · exact False.elim (leftNonempty empty)
  · rcases rightBoundary with ⟨empty,_same⟩ |⟨next,remaining,output,_after,reader,_suff⟩
    · exact False.elim (rightNonempty empty)
    · exact control_corridor_step_of_boundary_turns flow route leftPrincipal rightPrincipal
        leftControl rightControl previous next writer reader
end
end Lamping.AG
