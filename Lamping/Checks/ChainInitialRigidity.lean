import Lamping.Lamping.ChainInitialRigidity
import Lamping.Checks.SyntaxIncidence

namespace Lamping.Checks.ChainInitialRigidity
open AG Graph Lambda Lambda.Labelled
private abbrev term := initLabels (.app (.lam (.var 0)) (.lam (.var 0)))
private theorem closed : Closed term.erase := by
  rw [erase_initLabels]
  exact ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
private def leftVariable : SyntaxIncidence.Edge term := ⟨[.fn,.body],by decide⟩
private def rightVariable : SyntaxIncidence.Edge term := ⟨[.arg,.body],by decide⟩

theorem initial_binder_edges_distinguishable :
    ¬Nonempty (ChainIncidenceIso
      (chainSyntaxIncidence term closed [[.fn,.body]])
      (chainSyntaxIncidence term closed [[.arg,.body]])) := by
  rintro ⟨iso⟩
  have same := chainSyntaxIncidence_initial_selected_iff term closed (init_is_INIT _)
    [[.fn,.body]] [[.arg,.body]] iso leftVariable
  have impossible := same.mp (show leftVariable.val∈[[.fn,.body]] from by decide)
  exact (by decide : ¬leftVariable.val∈[[.arg,.body]]) impossible

/-- The usable claim compares actual occurrences, not abstract label sets. -/
theorem initial_edge_fixed
    (iso : ChainIncidenceIso
      (chainSyntaxIncidence term closed [[.fn,.body]])
      (chainSyntaxIncidence term closed [[.fn,.body]])) :
    (iso.edges ⟨leftVariable,by decide⟩).val=leftVariable :=
  iso.induced_edges_fixed (syntaxIncidence_label_injective term (init_is_INIT _).2) _

/-- Existing noninitial repeated-label data do not satisfy the distinctness
hypothesis; this explicitly prevents applying initial rigidity to histories. -/
theorem noninitial_labels_do_not_identify_occurrences :
    ∃ left right : SyntaxIncidence.Edge SyntaxIncidence.I.term,
      SyntaxIncidence.label SyntaxIncidence.I.term left=
        SyntaxIncidence.label SyntaxIncidence.I.term right ∧left≠right := by
  refine ⟨SyntaxIncidence.I.leftVariable,SyntaxIncidence.I.rightVariable,rfl,?_⟩
  intro same
  have paths := congrArg Subtype.val same
  cases paths

#print axioms AG.ChainIncidenceIso.induced_selected_iff
#print axioms syntaxIncidence_label_injective
#print axioms chainSyntaxIncidence_initial_selected_iff
#print axioms initial_binder_edges_distinguishable
#print axioms initial_edge_fixed
#print axioms noninitial_labels_do_not_identify_occurrences
end Lamping.Checks.ChainInitialRigidity
