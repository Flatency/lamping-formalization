import Lamping.Lambda.UniformOldNodeLabelSuffix
namespace Lamping.Lambda.Marked
open Labelled
/-- Equality of two marked current labels identifies the complete labels of
THIS pair of operational origins. It does not identify their coordinates. -/
theorem RelativeOldHistory.equal_marked_node_origin_labels
    {F ps : List Path} {m n : Marked} (old : RelativeOldHistory F ps m n)
    {d : Path →Option Label} {source target current otherCurrent : LTerm} {alpha : Label}
    {p q oldPosition otherOldPosition : Path}
    (aligned : DegreeAligned d m source) (labels : Labelled.History ps source target)
    (selected : ∀name∈F,d name=some alpha)
    (trace : BetaNodeHistoryPreimage labels p oldPosition)
    (otherTrace : BetaNodeHistoryPreimage labels q otherOldPosition)
    (lookup : target.subterm p=some current)
    (otherLookup : target.subterm q=some otherCurrent)
    (sourceSafe : source.OuterBarsSafe (fun payload=>payload≠alpha))
    (marked : ¬current.label.OuterBarsSafe (fun payload=>payload≠alpha))
    (same : current.label=otherCurrent.label) :
    ∃original otherOriginal,
      source.subterm oldPosition=some original ∧
      source.subterm otherOldPosition=some otherOriginal ∧
      original.label=otherOriginal.label := by
  have otherMarked : ¬otherCurrent.label.OuterBarsSafe (fun payload=>payload≠alpha) := by
    rw [←same];exact marked
  obtain ⟨original,pre,marker,atOriginal,safe,marks,equation,reversed⟩ :=
    old.node_last_marker aligned labels selected trace lookup sourceSafe marked
  obtain ⟨otherOriginal,otherPre,otherMarker,atOther,otherSafe,otherMarks,otherEquation,otherReversed⟩ :=
    old.node_last_marker aligned labels selected otherTrace otherLookup sourceSafe otherMarked
  have parsed := Label.readLetters_first_marker_of_splits (forward:=false)
    safe otherSafe marks otherMarks reversed otherReversed same
  exact ⟨original,otherOriginal,atOriginal,atOther,parsed.1⟩
#print axioms RelativeOldHistory.equal_marked_node_origin_labels
end Lamping.Lambda.Marked
