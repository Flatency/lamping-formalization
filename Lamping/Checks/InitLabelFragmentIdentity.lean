import Lamping.Lamping.InitLabelFragmentIdentity
import Lamping.Lamping.InitialFragmentReflection
import Lamping.Lamping.InitialMatching
import Lamping.Checks.SyntaxIncidence

namespace Lamping.Checks.InitLabelFragmentIdentity
open AG Graph Lambda Lambda.Labelled

/-- The initial auxiliary-separation base has an internally supplied actual
selector at every closed encoding, before any comparison is requested. -/
theorem every_initial_encoding_label_identity (term : Term) (closed : Closed term) (level : Nat) :
    ∃ selection : OccurrenceFragmentSelection (initLabels term) (encode level term).net (.inl ()),
    ∀ left right : SyntaxIncidence.Edge (initLabels term),
      SyntaxIncidence.label (initLabels term) left=SyntaxIncidence.label (initLabels term) right →
      (selection left).fragment.segments=(selection right).fragment.segments := by
  have labelledClosed : Closed (initLabels term).erase := by simpa only [erase_initLabels] using closed
  have matching : Matches (encode level term).net (.inl ()) (initLabels term).erase := by
    rw [erase_initLabels]
    exact encode_closed_matches term closed level
  obtain ⟨selection⟩ := matching.occurrence_fragment_selection labelledClosed
  exact ⟨selection,fun left right same=>(init_label_fragment_identity matching
    (init_is_INIT term) selection selection left right same).2⟩

/-- Without current INIT, a genuine encoded repeated-label term can have
equal labels and different physical fragments. This is not a counterexample
to reachable REP; it excludes dropping the current-INIT hypothesis above. -/
theorem noninitial_labels_can_have_different_physical_fragments :
    ∃ selection : OccurrenceFragmentSelection SyntaxIncidence.I.term
        (encode 0 SyntaxIncidence.I.term.erase).net (.inl ()),
      SyntaxIncidence.label SyntaxIncidence.I.term SyntaxIncidence.I.leftVariable=
        SyntaxIncidence.label SyntaxIncidence.I.term SyntaxIncidence.I.rightVariable ∧
      (selection SyntaxIncidence.I.leftVariable).fragment.segments≠
        (selection SyntaxIncidence.I.rightVariable).fragment.segments := by
  obtain ⟨selection⟩ := (encode_closed_matches SyntaxIncidence.I.term.erase
    SyntaxIncidence.I.closed 0).occurrence_fragment_selection SyntaxIncidence.I.closed
  refine ⟨selection,rfl,?_⟩
  intro same
  have paths := (selection SyntaxIncidence.I.leftVariable).initial_segments_injective
    (selection SyntaxIncidence.I.rightVariable) same
  cases paths

#print axioms init_label_fragment_identity
#print axioms init_label_different_fragments_impossible
#print axioms every_initial_encoding_label_identity
#print axioms noninitial_labels_can_have_different_physical_fragments
end Lamping.Checks.InitLabelFragmentIdentity
