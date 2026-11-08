import Lamping.Lamping.ChainInitialSequences
import Lamping.Lamping.InitialMatching

namespace Lamping.Checks.ChainInitialSequences
open AG Graph Lambda Lambda.Labelled
private abbrev term := initLabels (.app (.lam (.var 0)) (.lam (.var 0)))
private theorem closed : Closed term.erase := by
  rw [erase_initLabels]
  exact ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩

private theorem argumentChain : PrerequisiteChain term [.arg] [[.arg],[.fn]] :=
  .lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl)
private theorem variableChain : PrerequisiteChain term [.arg,.body] [[.arg],[.fn]] :=
  .var (rest:=[]) rfl rfl rfl rfl argumentChain

/-- The same nonpointed chain is read from a proper lambda occurrence or
from its bound variable. Actual starting syntax positions stay different. -/
noncomputable def actualIso : ChainIncidenceIso
    (chainSyntaxIncidence term closed [[.arg],[.fn]])
    (chainSyntaxIncidence term closed [[.arg],[.fn]]) := .refl _

theorem actual_initial_sequence_from_incidence :
    ([[.arg],[.fn]] : List Path)=[[.arg],[.fn]] :=
  chainSyntaxIncidence_initial_sequences term closed (init_is_INIT _) argumentChain variableChain actualIso

/-- Reversing the actual two-edge chain cannot be accepted as another
prerequisite chase. The rank obstruction is independent of edge labels. -/
theorem actual_reverse_is_not_a_chain :
    ¬PrerequisiteChain term [.arg] [[.fn],[.arg]] := by
  intro wrong
  have less := (List.pairwise_cons.mp wrong.edges_strict).1 [.arg] (by simp)
  change 3<0 at less
  omega

theorem actual_initial_canonical_block_bridge
    (left right : OccurrenceFragmentSelection term (encode 0 term.erase).net (.inl ())) :
    canonicalChainImage left argumentChain=canonicalChainImage right variableChain :=
  initial_iso_canonical_blocks (encode_closed_matches term.erase closed 0) closed
    (init_is_INIT _) argumentChain variableChain actualIso left right

/-- The selector exists from actual initial Matches; callers need not
provide fragment existence to consume the initial bridge. -/
theorem actual_initial_block_realization :
    ∃ selection : OccurrenceFragmentSelection term (encode 0 term.erase).net (.inl ()),
      canonicalChainImage selection argumentChain=canonicalChainImage selection variableChain := by
  have matching := encode_closed_matches term.erase closed 0
  obtain ⟨selection⟩ := matching.occurrence_fragment_selection closed
  exact ⟨selection,actual_initial_canonical_block_bridge selection selection⟩

#print axioms PrerequisiteChain.edges_strict
#print axioms PrerequisiteChain.eq_edges_of_membership
#print axioms chainSyntaxIncidence_initial_sequences
#print axioms initial_iso_canonical_blocks
#print axioms actual_reverse_is_not_a_chain
#print axioms actual_initial_canonical_block_bridge
#print axioms actual_initial_block_realization
end Lamping.Checks.ChainInitialSequences
