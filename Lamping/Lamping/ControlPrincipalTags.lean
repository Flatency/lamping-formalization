import Lamping.Lamping.PathLabelDeterminism
namespace Lamping.AG

/-- The three control kinds have disjoint principal marker images. -/
def Level.principalControl : Level → Op
  | .empty => .cro
  | .o _ | .star _ => .fan
  | .pair _ _ => .bra

/-- This tag is read from an actual control-principal writer, not inferred
from the printed label of an unrelated node. -/
theorem Traversal.control_principal_output {i : Nat} {op : Op}
    (control : op=.fan ∨op=.cro ∨op=.bra) {p : Port (.op op)} {a b : Context}
    (rule : Traversal i (.op op) p (.inl ()) a b) : (b.get i).principalControl=op := by
  rcases control with same |same |same <;> subst op
  all_goals cases rule with
    | direct passage => cases passage <;> simp [Context.replace,Level.principalControl]
    | inverse passage => cases passage

/-- Two actual controls joined at equal-index principals in a labelled path
must have the same kind. Mixed equal-index control obstructions are impossible. -/
theorem Traversal.equal_index_control_principals {i : Nat} {left right : Op}
    (leftControl : left=.fan ∨left=.cro ∨left=.bra)
    (rightControl : right=.fan ∨right=.cro ∨right=.bra)
    {p : Port (.op left)} {q : Port (.op right)} {a b c : Context}
    (leftTurn : Traversal i (.op left) p (.inl ()) a b)
    (rightTurn : Traversal i (.op right) (.inl ()) q b c) : left=right := by
  have first := leftTurn.control_principal_output leftControl
  have second := rightTurn.reverse.control_principal_output rightControl
  exact first.symm.trans second
end Lamping.AG
