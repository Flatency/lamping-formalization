import Lamping.Lamping.CanonicalChildDeparture
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {current : LTerm}
/-- Actual different parent nodes force different canonical child pieces.
Node identities come from specified rooted parent finishes, not labels. -/
theorem SourceEdgeFragment.ne_of_parent_nodes
    (matching : Matches g root current.erase)
    (left : SourceEdgeFragment current g root leftEdge p)
    (right : SourceEdgeFragment current g root rightEdge q)
    (leftRole : SourceDeparture leftTerm leftStep leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm rightStep rightEdge.fromPort)
    (leftParent rightParent : RootAccess g root)
    (leftWord : p=accessWord g leftParent.val++[leftStep])
    (rightWord : q=accessWord g rightParent.val++[rightStep])
    (leftNode rightNode : N) (leftPort : Port (g.label leftNode).sort) (rightPort : Port (g.label rightNode).sort)
    (leftFinish : leftParent.val.getLast?=some (g.wire (.inl ⟨leftNode,leftPort⟩)))
    (rightFinish : rightParent.val.getLast?=some (g.wire (.inl ⟨rightNode,rightPort⟩)))
    (different : leftNode≠rightNode) : left.segments≠right.segments := by
  obtain ⟨leftDeparture,leftHead⟩ := left.head_node_of_parent matching leftRole leftParent leftWord leftNode leftPort leftFinish
  obtain ⟨rightDeparture,rightHead⟩ := right.head_node_of_parent matching rightRole rightParent rightWord rightNode rightPort rightFinish
  intro same
  have heads := congrArg List.head? same
  rw [leftHead,rightHead] at heads
  exact different (congrArg Sigma.fst (Sum.inl.inj (Option.some.inj heads)))
end
end Lamping.AG
