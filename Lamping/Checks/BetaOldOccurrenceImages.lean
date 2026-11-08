import Lamping.Lamping.BetaOldOccurrenceImages
import Lamping.Checks.OldChainBetaFixture
namespace Lamping.Checks.BetaOldOccurrenceImages
open AG Graph Lambda Lambda.Labelled OldChainBetaFixture
/-- Two distinct real target child occurrences consume the comparison.
Their old coordinates are locked separately by the actual SAME history. -/
theorem actual_distinct_occurrences
    (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ()))
    (sourceSelection : OccurrenceFragmentSelection initial presentation.site.net (.inl ()))
    (targetSelection : OccurrenceFragmentSelection result presentation.site.reduce (.inl ())) :
    (targetSelection ⟨[.fn],rfl⟩).fragment.segments=(targetSelection ⟨[.arg],rfl⟩).fragment.segments ↔
      (sourceSelection ⟨[.arg,.fn],rfl⟩).fragment.segments=
        (sourceSelection ⟨[.arg,.arg],rfl⟩).fragment.segments := by
  have matching := presentation.sourceIso.matches (encode_closed_matches term closed 0)
  have inputs := presentation.sourceIso.rootInputs (encode_closed_independence term closed 0).rootInputs
  obtain ⟨originalFlow⟩ := encode_flowBalance term 0
  have flow := presentation.sourceIso.flowBalance originalFlow
  obtain ⟨originalBalance⟩ := encode_indexed_balance term 0
  have balance := presentation.sourceIso.indexed_balance originalBalance
  have transparency := presentation.sourceIso.transparency (encode_closed_transparency term closed 0)
  have selected (path : Path) (member : path∈([[]] : List Path)) :
      initial.degreeAt path=some (Labelled.Label.atom 1) := by
    have same := List.mem_singleton.mp member
    subst path;rfl

  let left := targetSelection ⟨[.fn],rfl⟩
  let right := targetSelection ⟨[.arg],rfl⟩
  have leftSafe := marker_free [.fn] (by simp) left.term left.occurrence.lookup
  have rightSafe : right.term.label.OuterBarsSafe (fun payload=>payload≠Labelled.Label.atom 1) := by
    have same : right.term=.lam (.atom 6) (.var (.atom 7) 0) := Option.some.inj right.occurrence.lookup.symm
    rw [same];trivial
  obtain ⟨leftOld,rightOld,leftNode,rightNode,leftLookup,rightLookup,leftTrace,rightTrace,comparison⟩ :=
    presentation.site.beta_marker_free_occurrence_pair (source:=initial) closed matching inputs flow rfl balance rfl
      transparency (relative presentation) (by simp [endpoint,Marked.Normal]) history
        complete.complete.1 (DegreeAligned.initial initial [[]]) selected sourceSelection left right leftSafe rightSafe
  have leftOrigin : BetaNodePreimage (.var (.atom 2) 0)
      (.app (.atom 3) (.lam (.atom 4) (.var (.atom 5) 0)) (.lam (.atom 6) (.var (.atom 7) 0)))
      [] [.fn] [.arg,.fn] := .copied (q:=[]) (relative:=[.fn]) rfl rfl
  have rightOrigin : BetaNodePreimage (.var (.atom 2) 0)
      (.app (.atom 3) (.lam (.atom 4) (.var (.atom 5) 0)) (.lam (.atom 6) (.var (.atom 7) 0)))
      [] [.arg] [.arg,.arg] := .copied (q:=[]) (relative:=[.arg]) rfl rfl
  have leftKnown : BetaNodeHistoryPreimage history [.fn] [.arg,.fn] :=
    .one (step:=turn) rfl leftOrigin (.nil result [.fn])
  have rightKnown : BetaNodeHistoryPreimage history [.arg] [.arg,.arg] :=
    .one (step:=turn) rfl rightOrigin (.nil result [.arg])
  have leftEqual := leftTrace.unique leftKnown
  have rightEqual := rightTrace.unique rightKnown
  subst leftOld
  subst rightOld
  exact comparison
#print axioms PathSite.beta_marker_free_occurrence_images
#print axioms PathSite.beta_exterior_occurrence_equality
#print axioms PathSite.beta_marker_free_occurrence_pair
#print axioms actual_distinct_occurrences
end Lamping.Checks.BetaOldOccurrenceImages
