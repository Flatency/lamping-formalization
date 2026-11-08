import Lamping.Lamping.PathLabelDeterminism
namespace Lamping.AG
open Graph

private theorem control_output_role {c : Op} {kind : Kind} {index : Nat} {p q : Port kind}
    {x : Aux c} {a b : Context} (sort : kind=.op c) (control : c=.fan ∨c=.cro ∨c=.bra)
    (role : HEq p (Sum.inr x : Port (.op c))) (rule : Traversal index kind p q a b) :
    HEq q (Sum.inl () : Port (.op c)) := by
  subst kind
  have same : p=.inr x := eq_of_heq role
  subst p
  rcases control with same |same |same <;> subst c <;> exact heq_of_eq rule.control_aux

private theorem canonical_turn {c : Op} {kind : Kind} {i j : Nat} {p q : Port kind}
    {x : Aux c} {a b : Context} (sort : kind=.op c) (index : i=j)
    (first : HEq p (Sum.inl () : Port (.op c))) (last : HEq q (Sum.inr x : Port (.op c)))
    (rule : Traversal i kind p q a b) : Traversal j (.op c) (.inl ()) (.inr x) a b := by
  subst kind
  subst j
  have hp : p=.inl () := eq_of_heq first
  have hq : q=.inr x := eq_of_heq last
  simpa only [hp,hq] using rule

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

private theorem no_boundary_output {x y : Endpoint g} {a b : Context}
    (turn : LabelledTurn g x y a b) (boundary : B) : y≠.inr (.inl boundary) := by
  cases turn <;> (intro impossible; cases impossible)

theorem Labelling.boundary_last {es : List (Endpoint g)} {a b : Context}
    (labels : Labelling g es a b) (boundary : B)
    (finish : es.getLast?=some (.inr (.inl boundary))) : es=[.inr (.inl boundary)] ∧a=b := by
  induction labels with
  | single e a => exact ⟨congrArg (·::[]) (Option.some.inj finish),rfl⟩
  | cons turn tail ih =>
    obtain ⟨same,_⟩ := ih (by simpa only [List.getLast?_cons_cons] using finish)
    have head := congrArg List.head? same
    simp only [List.head?_cons,Option.some.injEq] at head
    exact False.elim (no_boundary_output turn boundary head)

private theorem Labelling.last_turn (pre : List (Endpoint g)) (last : Endpoint g)
    {a b : Context} (labels : Labelling g (pre++[last]) a b) (nonempty : pre≠[]) :
    ∃ previous middle,pre.getLast?=some previous ∧Labelling g pre a middle ∧
      LabelledTurn g (g.wire previous) last middle b := by
  induction pre generalizing a with
  | nil => exact False.elim (nonempty rfl)
  | cons x pre ih =>
    cases pre with
    | nil => cases labels with
      | cons turn tail => cases tail; exact ⟨x,_,rfl,.single _ _,turn⟩
    | cons y pre => cases labels with
      | cons turn tail =>
        obtain ⟨previous,middle,finish,first,lastTurn⟩ := ih tail (by simp)
        exact ⟨previous,middle,by simpa only [List.getLast?_cons_cons] using finish,.cons turn first,lastTurn⟩

/-- This is a finite backward incidence theorem at a control leaf of a rule
RHS. A real labelled prefix ending at its auxiliary port has exactly two
segments. The principal-to-boundary connection is explicit, not completion. -/
theorem Labelling.control_leaf_prefix {es : List (Endpoint g)} {a b : Context}
    (labels : Labelling g es a b) (entry boundary : B)
    (start : es.head?=some (.inr (.inl entry)))
    (node : N) (c : Op) (index : Nat) (lab : g.label node=label c index)
    (control : c=.fan ∨c=.cro ∨c=.bra)
    (primary aux : Port (g.label node).sort) (x : Aux c)
    (primaryRole : HEq primary (Sum.inl () : Port (.op c)))
    (auxRole : HEq aux (Sum.inr x : Port (.op c)))
    (connection : g.wire (.inl ⟨node,primary⟩)=.inr (.inl boundary))
    (finish : es.getLast?=some (.inl ⟨node,aux⟩)) :
    entry=boundary ∧es=[.inr (.inl boundary),.inl ⟨node,aux⟩] ∧
      Traversal index (.op c) (.inl ()) (.inr x) a b := by
  obtain ⟨pre,split⟩ := List.getLast?_eq_some_iff.mp finish
  have nonempty : pre≠[] := by
    intro empty
    rw [split,empty] at start
    cases start
  rw [split] at labels
  obtain ⟨previous,middle,preLast,preLabels,turn⟩ := labels.last_turn pre _ nonempty
  obtain ⟨port,arrival,reverseRule⟩ := turn.reverse.from_node node aux rfl
  have sameRole := control_output_role (congrArg Label.sort lab) control auxRole reverseRule
  have portEq : port=primary := eq_of_heq (sameRole.trans primaryRole.symm)
  subst port
  have before : previous=.inr (.inl boundary) := by
    have wired := congrArg g.wire.mate arrival
    rw [Pairing.involutive,connection] at wired
    exact wired
  rw [before] at preLast
  obtain ⟨preEq,middleEq⟩ := preLabels.boundary_last boundary preLast
  subst middle
  have full : es=[.inr (.inl boundary),.inl ⟨node,aux⟩] := by rw [split,preEq]; rfl
  have boundaryEq : entry=boundary := by
    rw [full] at start
    exact (Sum.inl.inj (Sum.inr.inj (Option.some.inj start))).symm
  refine ⟨boundaryEq,full,?_⟩
  exact canonical_turn (congrArg Label.sort lab) (congrArg Label.index lab) primaryRole auxRole reverseRule.reverse
end
end Lamping.AG
