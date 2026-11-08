import Lamping.Lamping.UniformOldChainIncidencePreimages
import Lamping.Checks.OldChainBetaFixture
namespace Lamping.Checks.OldChainBetaFixture
open AG Graph Lambda Lambda.Labelled
private abbrev argument : LTerm :=
  .app (.atom 3) (.lam (.atom 4) (.var (.atom 5) 0)) (.lam (.atom 6) (.var (.atom 7) 0))

/-- The incidence witness and the ordered physical ancestry refer to the
SAME original ARG/FUNCTION occurrence of this nonempty actual chain. -/
theorem actual_same_ordered_incidence :
    BetaNodeHistoryPreimage history [] [.arg] ∧
    BetaEdgeHistoryPreimages history [[.fn]] [[.arg,.fn]] ∧
    ChainIncidenceIsomorphic (chainSyntaxIncidence result (history.closed closed) [[.fn]])
      (chainSyntaxIncidence initial closed [[.arg,.fn]]) := by
  have selected (path : Path) (member : path∈([[]] : List Path)) :
      initial.degreeAt path=some (Labelled.Label.atom 1) := by
    have same := List.mem_singleton.mp member
    subst path;rfl
  obtain ⟨oldStart,oldEdges,_oldChain,startTrace,edgeTraces,_labels,_length,incidence⟩ :=
    complete.complete.1.marker_free_chain_incidence_preimages (source:=initial) (target:=result) closed (history.closed closed)
      (DegreeAligned.initial initial [[]]) history selected targetChain marker_free
  have startOrigin : BetaNodePreimage (.var (.atom 2) 0) argument [] [] [.arg] :=
    .copied (q:=[]) (relative:=[]) rfl rfl
  have readOrigin : BetaNodePreimage (.var (.atom 2) 0) argument [] [.fn] [.arg,.fn] :=
    .copied (q:=[]) (relative:=[.fn]) rfl rfl
  have knownStart : BetaNodeHistoryPreimage history [] [.arg] :=
    .one (step:=turn) rfl startOrigin (.nil result [])
  have knownReads : BetaEdgeHistoryPreimages history [[.fn]] [[.arg,.fn]] :=
    .cons (.one (step:=turn) rfl readOrigin (.nil result [.fn])) .nil
  have sameStart := startTrace.unique knownStart
  have sameEdges := edgeTraces.unique knownReads
  subst oldStart
  subst oldEdges
  exact ⟨startTrace,edgeTraces,incidence⟩

#print axioms Marked.RelativeOldHistory.marker_free_chain_incidence_preimages
#print axioms actual_same_ordered_incidence
end Lamping.Checks.OldChainBetaFixture
