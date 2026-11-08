import Lamping.Lamping.PairedMarkerLeafGeometry

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- The actual safe FIRST in a paired event evaluates to its OWN original
source occurrence fragment. No label identifies a current coordinate, and
no source-chain iso or physical equality is supplied by the caller. -/
theorem paired_marker_first_fragment
    (leaf : DirectedMarkerLeafOutput F source degree forward ps word)
    (paired : PairedMarkerEventGeometry leaf (initLabels source.erase) localTarget)
    (matching : Matches g root source.erase)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (selection : SourceEdgeSelection (initLabels source.erase) g root)
    (physical : BetaEdge g) :
    ∃ position : Position source.erase,∃ oldNode,
      source.subterm position.val=some oldNode ∧
      BetaNodeHistoryPreimage leaf.event.labels leaf.first position.val ∧
      selection.evalLabel physical paired.firstNode.label=(sourceSelection position).fragment.segments ∧
      accessWord g (selection.evalLabel physical paired.firstNode.label)=[] ∧
      selection.evalLabel physical paired.firstNode.label≠[] := by
  obtain ⟨oldPosition,oldNode,lookup,trace,evaluation⟩ :=
    selection.marker_free_local_evaluation matching leaf.event.beforeOld (DegreeAligned.initial source F)
      leaf.event.labels paired.prefixLabels selected leaf.firstLookup paired.firstLookup leaf.firstSafe physical
  let position : Position source.erase := ⟨oldPosition,by rw [←LTerm.erase_subterm,lookup];rfl⟩
  have same := evaluation (sourceSelection position)
  refine ⟨position,oldNode,lookup,trace,same,?_,?_⟩
  · rw [same];exact (sourceSelection position).fragment.emptyWord
  · rw [same]
    intro empty
    have start := (sourceSelection position).fragment.start
    rw [empty] at start
    cases start
end
#print axioms paired_marker_first_fragment
end Lamping.AG
