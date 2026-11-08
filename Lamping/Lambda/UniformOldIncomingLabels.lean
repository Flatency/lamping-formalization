import Lamping.Lambda.SafeIncomingHistory
import Lamping.Lambda.UniformOldCreatedIncomingLabels
namespace Lamping.Lambda.Marked
open Labelled

/-- Equality of arbitrary current incoming labels preserves the full labels
of THIS two operational origins. Safety is tested only at these occurrences. -/
theorem RelativeOldHistory.equal_node_origin_labels
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
    (same : current.label=otherCurrent.label) :
    ∃original otherOriginal,
      source.subterm oldPosition=some original ∧
      source.subterm otherOldPosition=some otherOriginal ∧
      original.label=otherOriginal.label := by
  classical
  by_cases safe : current.label.OuterBarsSafe (fun payload=>payload≠alpha)
  · have otherSafe : otherCurrent.label.OuterBarsSafe (fun payload=>payload≠alpha) := by
      rw [←same];exact safe
    obtain ⟨original,atOriginal,equal⟩ :=
      (old.safe_incoming_uncreated aligned selected trace lookup safe).source_label lookup
    obtain ⟨otherOriginal,atOther,otherEqual⟩ :=
      (old.safe_incoming_uncreated aligned selected otherTrace otherLookup otherSafe).source_label otherLookup
    exact ⟨original,otherOriginal,atOriginal,atOther,equal.trans (same.trans otherEqual.symm)⟩
  · exact old.equal_marked_node_origin_labels aligned labels selected trace otherTrace
      lookup otherLookup sourceSafe safe same
end Lamping.Lambda.Marked
