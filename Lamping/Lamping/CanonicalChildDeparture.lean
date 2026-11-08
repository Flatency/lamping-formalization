import Lamping.Lamping.ChainFragmentUniqueness
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {current : LTerm}
/-- The actual canonical child cut has the SAME proper node as the supplied
actual parent access. A node label or bare endpoint equality is not used to
choose a different rooted access. -/
theorem SourceEdgeFragment.head_node_of_parent
    (fragment : SourceEdgeFragment current g root edge p)
    (matching : Matches g root current.erase)
    (role : SourceDeparture term step edge.fromPort)
    (parent : RootAccess g root) (word : p=accessWord g parent.val++[step])
    (node : N) (port : Port (g.label node).sort)
    (finish : parent.val.getLast?=some (g.wire (.inl ⟨node,port⟩))) :
    ∃ departure : Port (g.label node).sort,
      fragment.segments.head?=some (.inl ⟨node,departure⟩) := by
  have actualWord := fragment.word.trans word
  obtain ⟨actualNode,ctx,departure,tail,_roles,actualFinish,split,_forward,_assignments⟩ :=
    matching.syntax_child_fragment parent fragment.access step actualWord
  have actualPrefix := fragment.child_prefix matching role parent word
  have actualSegments : fragment.segments=(.inl ⟨actualNode,departure⟩)::tail := by
    exact List.append_cancel_left (actualPrefix.2.symm.trans split)
  have endpoints := Option.some.inj (actualFinish.symm.trans finish)
  have reversed := congrArg g.wire.mate endpoints
  simp only [Pairing.involutive] at reversed
  have nodes : actualNode=node := congrArg Sigma.fst (Sum.inl.inj reversed)
  subst actualNode
  exact ⟨departure,by rw [actualSegments];rfl⟩
end
end Lamping.AG
