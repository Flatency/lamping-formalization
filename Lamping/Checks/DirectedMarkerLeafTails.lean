import Lamping.Lambda.DirectedMarkerLeafTails
import Lamping.Checks.DirectedMarkerLeafWords
namespace Lamping.Checks.DirectedMarkerLeafTailsChecks
open Lambda Lambda.Labelled
namespace Distinct
open UniformOldCreatedIncomingLabelsChecks.Distinct

theorem leftProduced : Nonempty
    (DirectedMarkerLeafOutput F source (.atom 7) false [left,right] (leftNode.label.readLetters false)) :=
  old.earliest_marker_leaf_output labels selected source_safe (start:=left) (before:=[]) .refl
    ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩ rfl marked (by intro e member;cases member)

theorem actual_pair_full_tails : ∃
    (leftLeaf rightLeaf : DirectedMarkerLeafOutput F source (.atom 7) false [left,right] (leftNode.label.readLetters false)), ∃leftTail rightTail,
    ExactMarkerLeafTail leftLeaf leftTail ∧ExactMarkerLeafTail rightLeaf rightTail ∧
    leftLeaf.firstNode.label=rightLeaf.firstNode.label ∧leftLeaf.marker=rightLeaf.marker ∧
    leftTail++leftLeaf.continuation=rightTail++rightLeaf.continuation := by
  obtain ⟨leftLeaf⟩ := leftProduced
  obtain ⟨rightLeaf⟩ := DirectedMarkerLeafWordsChecks.NonemptyPrefix.produced
  obtain ⟨l,r,lc,rc,first,marker,tail⟩ := leftLeaf.compare_full_tails rightLeaf rfl
  exact ⟨leftLeaf,rightLeaf,l,r,lc,rc,first,marker,tail⟩

theorem actual_original_first_labels : ∃
    (leftLeaf rightLeaf : DirectedMarkerLeafOutput F source (.atom 7) false [left,right] (leftNode.label.readLetters false)), ∃lp rp ln rn,
    source.subterm lp=some ln ∧source.subterm rp=some rn ∧
    BetaNodeHistoryPreimage leftLeaf.event.labels leftLeaf.first lp ∧
    BetaNodeHistoryPreimage rightLeaf.event.labels rightLeaf.first rp ∧ln.label=rn.label := by
  obtain ⟨leftLeaf⟩ := leftProduced
  obtain ⟨rightLeaf⟩ := DirectedMarkerLeafWordsChecks.NonemptyPrefix.produced
  obtain ⟨lp,rp,ln,rn,atL,atR,traceL,traceR,equal⟩ := leftLeaf.compare_original_first_labels rightLeaf selected rfl
  exact ⟨leftLeaf,rightLeaf,lp,rp,ln,rn,atL,atR,traceL,traceR,equal⟩

theorem actual_distinct_current_words : left≠right ∧
    target.subterm left=some leftNode ∧target.subterm right=some leftNode ∧
    INIT original ∧History [[],left,right] original target :=
  ⟨by decide,rfl,rfl,initial,globalHistory.append labels⟩
end Distinct

namespace Overlap
open DirectedReadingDecompositionChecks
noncomputable def actualLeaf (forward : Bool) :=
  Classical.choice (DirectedMarkerLeafWordsChecks.RootOverlap.produced forward)

theorem actual_full_tail (forward : Bool) : ∃tail,
    ExactMarkerLeafTail (actualLeaf forward) tail ∧
    result.label.readLetters forward=(actualLeaf forward).firstNode.label.readLetters forward++
      (actualLeaf forward).marker::(tail++(actualLeaf forward).continuation) :=
  (actualLeaf forward).full_tail

theorem actual_opposite_words_differ : result.label.readLetters true≠result.label.readLetters false := by decide

theorem actual_two_separators :
    result.label.readLetters true=[.atom 1,.over (.atom 2),.atom 3,.under (.atom 2),.atom 4] ∧
    result.label.readLetters false=[.atom 4,.under (.atom 2),.atom 3,.over (.atom 2),.atom 1] := actual_overlap_words
end Overlap

namespace Continued
noncomputable def actualLeaf (forward : Bool) :=
  Classical.choice (DirectedMarkerLeafWordsChecks.MarkedDescent.produced forward)

/-- This real two-event OLD producer exercises marked-first descent. We
compare the complete tail with its continuation, never cancel that continuation. -/
theorem actual_full_continued_tail (forward : Bool) : ∃tail,
    ExactMarkerLeafTail (actualLeaf forward) tail ∧
    (actualLeaf forward).current.label.readLetters forward++(actualLeaf forward).continuation=
      (actualLeaf forward).firstNode.label.readLetters forward++
        (actualLeaf forward).marker::(tail++(actualLeaf forward).continuation) := by
  obtain ⟨tail,kind,equation⟩ := (actualLeaf forward).full_tail
  exact ⟨tail,kind,(actualLeaf forward).equation.symm.trans equation⟩
end Continued

#print axioms Distinct.actual_pair_full_tails
#print axioms Distinct.actual_original_first_labels
#print axioms Distinct.actual_distinct_current_words
#print axioms Overlap.actual_full_tail
#print axioms Overlap.actual_opposite_words_differ
#print axioms Overlap.actual_two_separators
#print axioms Continued.actual_full_continued_tail
end Lamping.Checks.DirectedMarkerLeafTailsChecks
