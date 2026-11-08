import Lamping.Lamping.CanonicalChildDeparture
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
private theorem SyntaxChildPorts.step_of_departure
    (left : SyntaxChildPorts kind ctx departure step)
    (right : SyntaxChildPorts kind otherCtx departure otherStep) : step=otherStep := by
  cases left <;> cases right <;> rfl
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {current : LTerm}
/-- A literal child piece fixes its actual syntax departure direction.
No occurrence identity or arbitrary access completion is asserted. -/
theorem SourceEdgeFragment.child_step_eq_of_segments_eq
    (matching : Matches g root current.erase)
    (left : SourceEdgeFragment current g root leftEdge p)
    (right : SourceEdgeFragment current g root rightEdge q)
    (leftRole : SourceDeparture leftTerm leftStep leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm rightStep rightEdge.fromPort)
    (leftParent rightParent : RootAccess g root)
    (leftWord : p=accessWord g leftParent.val++[leftStep])
    (rightWord : q=accessWord g rightParent.val++[rightStep])
    (same : left.segments=right.segments) : leftStep=rightStep := by
  obtain ⟨ln,lc,ld,ltail,lroles,_lfinish,lsplit,_lf,_la⟩ := matching.syntax_child_fragment
    leftParent left.access leftStep (left.word.trans leftWord)
  obtain ⟨rn,rc,rd,rtail,rroles,_rfinish,rsplit,_rf,_ra⟩ := matching.syntax_child_fragment
    rightParent right.access rightStep (right.word.trans rightWord)
  have lcut := left.child_prefix matching leftRole leftParent leftWord
  have rcut := right.child_prefix matching rightRole rightParent rightWord
  have lp : left.segments=(.inl ⟨ln,ld⟩)::ltail :=
    List.append_cancel_left (lcut.2.symm.trans lsplit)
  have rp : right.segments=(.inl ⟨rn,rd⟩)::rtail :=
    List.append_cancel_left (rcut.2.symm.trans rsplit)
  rw [lp,rp] at same
  have endpoints : (⟨ln,ld⟩ : NodePort signature N g.label)=⟨rn,rd⟩ :=
    Sum.inl.inj (List.cons.inj same).1
  have nodes : ln=rn := congrArg Sigma.fst endpoints
  subst rn
  have dep : ld=rd := eq_of_heq (Sigma.mk.inj endpoints).2
  rw [←dep] at rroles
  exact lroles.step_of_departure rroles
/-- Different actual child steps separate pieces for all terminals. -/
theorem SourceEdgeFragment.ne_of_child_steps
    (matching : Matches g root current.erase)
    (left : SourceEdgeFragment current g root leftEdge p)
    (right : SourceEdgeFragment current g root rightEdge q)
    (leftRole : SourceDeparture leftTerm leftStep leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm rightStep rightEdge.fromPort)
    (leftParent rightParent : RootAccess g root)
    (leftWord : p=accessWord g leftParent.val++[leftStep])
    (rightWord : q=accessWord g rightParent.val++[rightStep])
    (different : leftStep≠rightStep) : left.segments≠right.segments := by
  exact fun same=>different (left.child_step_eq_of_segments_eq matching right leftRole rightRole
    leftParent rightParent leftWord rightWord same)
end
#print axioms SourceEdgeFragment.child_step_eq_of_segments_eq
#print axioms SourceEdgeFragment.ne_of_child_steps
end Lamping.AG
