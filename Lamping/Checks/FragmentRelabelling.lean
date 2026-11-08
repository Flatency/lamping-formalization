import Lamping.Lamping.FragmentRelabelling
import Lamping.Lamping.BetaEncodingIso
import Lamping.Lamping.InitialMatching
namespace Lamping.Checks.FragmentRelabelling
open AG Graph Lambda Lambda.Labelled
private def repeated : LTerm := .app (.atom 9)
  (.lam (.atom 9) (.var (.atom 9) 0)) (.lam (.atom 9) (.var (.atom 9) 0))
private abbrev initial := initLabels identityApp
private theorem actualMatching : Matches actualBetaSite.net (.inl ()) identityApp :=
  betaEncodingIso.matches (encode_closed_matches identityApp
    ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩ 0)
private def rootPosition (t : LTerm) : Position t.erase := ⟨[],by cases t <;> rfl⟩
private def argumentPosition : Position repeated.erase := ⟨[.arg],rfl⟩
private def initialArgumentPosition : Position initial.erase := ⟨[.arg],rfl⟩
private def variablePosition : Position repeated.erase := ⟨[.arg,.body],rfl⟩
private def initialVariablePosition : Position initial.erase := ⟨[.arg,.body],rfl⟩
private def repeatedChain : PrerequisiteChain repeated [.arg] [[.arg],[.fn]] :=
  .lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl)
private def initialChain : PrerequisiteChain initial [.arg] [[.arg],[.fn]] :=
  .lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl)

theorem repeated_annotation_not_initial : ¬INIT repeated := by
  simp [INIT,repeated,LTerm.labels]

/-- Two arbitrary selectors over the SAME actual encoded graph agree at
the root, the argument lambda and its bound-variable occurrence, despite
repeated labels versus fresh INIT labels. No selector is fixed by a fixture. -/
theorem actual_arbitrary_selectors
    (first : OccurrenceFragmentSelection repeated actualBetaSite.net (.inl ()))
    (second : OccurrenceFragmentSelection initial actualBetaSite.net (.inl ())) :
    (first (rootPosition repeated)).fragment.segments=
      (second (rootPosition initial)).fragment.segments ∧
    (first argumentPosition).fragment.segments=(second initialArgumentPosition).fragment.segments ∧
    (first variablePosition).fragment.segments=(second initialVariablePosition).fragment.segments := by
  have left : Matches actualBetaSite.net (.inl ()) repeated.erase := actualMatching
  have right : Matches actualBetaSite.net (.inl ()) initial.erase := actualMatching
  exact ⟨OccurrenceFragment.segments_unique_of_matches left right _ _,
    OccurrenceFragment.segments_unique_of_matches left right _ _,
    OccurrenceFragment.segments_unique_of_matches left right _ _⟩

/-- The real two-edge chain has the same canonical image under both
annotations. No chain-isomorphism or family-history conclusion is assumed. -/
theorem actual_two_edge_chain_image
    (first : OccurrenceFragmentSelection repeated actualBetaSite.net (.inl ()))
    (second : OccurrenceFragmentSelection initial actualBetaSite.net (.inl ())) :
    canonicalChainImage first repeatedChain=canonicalChainImage second initialChain :=
  canonicalChainImage_same_positions actualMatching actualMatching first second repeatedChain initialChain

#print axioms OccurrenceFragment.segments_unique_of_matches
#print axioms canonicalChainImage_same_positions
#print axioms repeated_annotation_not_initial
#print axioms actual_arbitrary_selectors
#print axioms actual_two_edge_chain_image
end Lamping.Checks.FragmentRelabelling
