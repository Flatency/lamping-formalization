import Lamping.Lamping.InitialFragmentReflection
import Lamping.Lamping.InitialMatching

namespace Lamping.Checks.InitialFragmentReflection
open AG Graph Lambda Lambda.Labelled

/-- A genuine initial graph with Fan sharing: both variable edges leave
one application and bind to one lambda. Every label intentionally repeats. -/
private def term : LTerm := .lam (.atom 9)
  (.app (.atom 9) (.var (.atom 9) 0) (.var (.atom 9) 0))
private theorem closed : Closed term.erase :=
  ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
private abbrev net := (encode 0 term.erase).net
private def functionVariable : Position term.erase := ⟨[.body,.fn],by decide⟩
private def argumentVariable : Position term.erase := ⟨[.body,.arg],by decide⟩

theorem actual_shared_departures_distinguish_occurrences
    (selection : OccurrenceFragmentSelection term net (.inl ())) :
    (selection functionVariable).fragment.fromEndpoint≠
        (selection argumentVariable).fragment.fromEndpoint ∧
      (selection functionVariable).fragment.segments≠
        (selection argumentVariable).fragment.segments := by
  constructor
  · intro same
    have paths := (selection functionVariable).initial_start_injective
      (selection argumentVariable) same
    cases paths
  · intro same
    have paths := (selection functionVariable).initial_segments_injective
      (selection argumentVariable) same
    cases paths

/-- Fragment existence is supplied by the genuine initial Matches theorem;
repeated labels do not identify the two physical departure paths. -/
theorem actual_shared_fragment_realization :
    ∃ selection : OccurrenceFragmentSelection term net (.inl ()),
      (selection functionVariable).fragment.segments≠
        (selection argumentVariable).fragment.segments := by
  obtain ⟨selection⟩ := (encode_closed_matches term.erase closed 0).occurrence_fragment_selection closed
  exact ⟨selection,(actual_shared_departures_distinguish_occurrences selection).2⟩

/-- The reflection theorem deliberately needs no INIT assumption: this
fixture has repeated node labels and is therefore not initially labelled. -/
theorem fixture_is_not_INIT : ¬INIT term := by
  intro initial
  have duplicate := initial.2
  simp [term,LTerm.labels] at duplicate

#print axioms OccurrenceFragment.initial_start_address
#print axioms OccurrenceFragment.initial_start_injective
#print axioms OccurrenceFragment.initial_segments_injective
#print axioms actual_shared_departures_distinguish_occurrences
#print axioms actual_shared_fragment_realization
#print axioms fixture_is_not_INIT
end Lamping.Checks.InitialFragmentReflection
