import Lamping.Lamping.ControlCorridorEndpoints
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

private theorem proper_not_control {node : N}
    (proper : (g.label node).sort=.op .app ∨(g.label node).sort=.op .lam) :
    ¬IsControlNode (g:=g) node := by
  rintro ⟨op,shape,control⟩
  rcases proper with app|lam
  · have eq:=Kind.op.inj (app.symm.trans shape)
    subst op
    rcases control with h|h|h <;> cases h
  · have eq:=Kind.op.inj (lam.symm.trans shape)
    subst op
    rcases control with h|h|h <;> cases h

private theorem proper_stop {node : N} {port : Port (g.label node).sort} {e f : Endpoint g}
    (proper : (g.label node).sort=.op .app ∨(g.label node).sort=.op .lam)
    (finish : e=g.wire (.inl ⟨node,port⟩)) : ¬ControlOnlyTurn (g:=g) e f := by
  intro turn
  have arrives : g.wire e=.inl ⟨node,port⟩ := by rw [finish,g.wire.involutive]
  exact proper_not_control proper (turn.arrival_control node port arrives)

private theorem proper_prefix_eq {xs ys after other : List (Endpoint g)}
    (xn : xs≠[]) (yn : ys≠[])
    (xc : ∀e f,(e,f)∈xs.zip xs.tail →ControlOnlyTurn (g:=g) e f)
    (yc : ∀e f,(e,f)∈ys.zip ys.tail →ControlOnlyTurn (g:=g) e f)
    (xe : ∃(node : N) (port : Port (g.label node).sort),
      ((g.label node).sort=.op .app ∨(g.label node).sort=.op .lam) ∧
        xs.getLast?=some (g.wire (.inl ⟨node,port⟩)))
    (ye : ∃(node : N) (port : Port (g.label node).sort),
      ((g.label node).sort=.op .app ∨(g.label node).sort=.op .lam) ∧
        ys.getLast?=some (g.wire (.inl ⟨node,port⟩)))
    (same : xs++after=ys++other) : xs=ys := by
  induction xs generalizing ys with
  | nil => exact False.elim (xn rfl)
  | cons e es ih =>
    cases ys with
    | nil => exact False.elim (yn rfl)
    | cons f fs =>
      have pair:=List.cons.inj same
      have head:=pair.1
      subst f
      cases es with
      | nil =>
        cases fs with
        | nil => rfl
        | cons f fs =>
          obtain ⟨node,port,proper,finish⟩:=xe
          exact False.elim (proper_stop proper (Option.some.inj finish) (yc e f (by simp)))
      | cons next es =>
        cases fs with
        | nil =>
          obtain ⟨node,port,proper,finish⟩:=ye
          exact False.elim (proper_stop proper (Option.some.inj finish) (xc e next (by simp)))
        | cons second fs =>
          have rest := ih (ys:=second::fs) (by simp) (by simp)
            (by intro a b member;exact xc a b (List.mem_cons_of_mem _ member))
            (by intro a b member;exact yc a b (List.mem_cons_of_mem _ member))
            (by simpa only [List.getLast?_cons_cons] using xe)
            (by simpa only [List.getLast?_cons_cons] using ye) pair.2
          exact congrArg (List.cons e) rest

/-- Proper final arrivals determine literal nonempty control-block boundaries.
This parses physical blocks only; it does not decode atom/bar labels. -/
theorem proper_ended_control_blocks_unique
    {left right : List (List (Endpoint g))}
    (leftRegular : ∀block∈left,block≠[] ∧
      (∀ e f,(e,f)∈block.zip block.tail →ControlOnlyTurn (g:=g) e f) ∧
      ∃(node : N) (port : Port (g.label node).sort),
        ((g.label node).sort=.op .app ∨(g.label node).sort=.op .lam) ∧
          block.getLast?=some (g.wire (.inl ⟨node,port⟩)))
    (rightRegular : ∀block∈right,block≠[] ∧
      (∀ e f,(e,f)∈block.zip block.tail →ControlOnlyTurn (g:=g) e f) ∧
      ∃(node : N) (port : Port (g.label node).sort),
        ((g.label node).sort=.op .app ∨(g.label node).sort=.op .lam) ∧
          block.getLast?=some (g.wire (.inl ⟨node,port⟩)))
    (same : left.flatten=right.flatten) : left=right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons y ys =>
      have empty : y=[] := (List.append_eq_nil_iff.mp same.symm).1
      exact False.elim ((rightRegular y List.mem_cons_self).1 empty)
  | cons x xs ih =>
    cases right with
    | nil =>
      have empty : x=[] := (List.append_eq_nil_iff.mp same).1
      exact False.elim ((leftRegular x List.mem_cons_self).1 empty)
    | cons y ys =>
      have lr:=leftRegular x List.mem_cons_self
      have rr:=rightRegular y List.mem_cons_self
      have head:=proper_prefix_eq lr.1 rr.1 lr.2.1 rr.2.1 lr.2.2 rr.2.2 same
      subst y
      have tail : xs.flatten=ys.flatten := List.append_cancel_left same
      have rest:=ih
        (by intro a member;exact leftRegular a (List.mem_cons_of_mem _ member))
        (by intro a member;exact rightRegular a (List.mem_cons_of_mem _ member)) tail
      exact congrArg (List.cons x) rest
end
#print axioms proper_ended_control_blocks_unique
end Lamping.AG
