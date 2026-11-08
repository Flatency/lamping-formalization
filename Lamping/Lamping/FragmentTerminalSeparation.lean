import Lamping.Lamping.ChainFragmentUniqueness
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {current : LTerm}
/-- Literal concatenation and the actual fragment finish identify its last edge, including root fragments. -/
theorem SourceEdgeFragment.segments_last_eq_access_last
    (fragment : SourceEdgeFragment current g root edge position) :
    fragment.segments.getLast?=fragment.access.val.getLast? := by
  rw [fragment.literal,List.getLast?_append,fragment.finish]
  rfl
/-- Different actual terminal ports separate literal pieces, without any parent restriction. -/
theorem SourceEdgeFragment.ne_of_terminal_ports
    (left : SourceEdgeFragment current g root leftEdge p)
    (right : SourceEdgeFragment current g root rightEdge q)
    (leftPort rightPort : NodePort signature N g.label)
    (leftFinish : left.access.val.getLast?=some (g.wire (.inl leftPort)))
    (rightFinish : right.access.val.getLast?=some (g.wire (.inl rightPort)))
    (different : leftPort≠rightPort) : left.segments≠right.segments := by
  intro same
  have lasts := congrArg List.getLast? same
  rw [left.segments_last_eq_access_last,right.segments_last_eq_access_last,
    leftFinish,rightFinish] at lasts
  have endpoints := congrArg g.wire (Option.some.inj lasts)
  simp only [Pairing.involutive] at endpoints
  exact different (Sum.inl.inj endpoints)
/-- Distinct terminal nodes are a sufficient special case. -/
theorem SourceEdgeFragment.ne_of_terminal_nodes
    (left : SourceEdgeFragment current g root leftEdge p)
    (right : SourceEdgeFragment current g root rightEdge q)
    (leftNode rightNode : N) (leftPort : Port (g.label leftNode).sort)
    (rightPort : Port (g.label rightNode).sort)
    (leftFinish : left.access.val.getLast?=some (g.wire (.inl ⟨leftNode,leftPort⟩)))
    (rightFinish : right.access.val.getLast?=some (g.wire (.inl ⟨rightNode,rightPort⟩)))
    (different : leftNode≠rightNode) : left.segments≠right.segments := by
  exact left.ne_of_terminal_ports right ⟨leftNode,leftPort⟩ ⟨rightNode,rightPort⟩
    leftFinish rightFinish (fun same=>different (congrArg Sigma.fst same))
end
#print axioms SourceEdgeFragment.segments_last_eq_access_last
#print axioms SourceEdgeFragment.ne_of_terminal_ports
#print axioms SourceEdgeFragment.ne_of_terminal_nodes
end Lamping.AG
