import Lamping.Lambda.EarliestReadingMarker
import Lamping.Lambda.UniformOldNodeLabelSuffix
namespace Lamping.Lambda.Labelled

/-- The other-last edge belongs to THIS reading event, and is traced through
THIS actual prefix. It is not the origin of the created incoming edge. -/
theorem SelectedOldTurn.other_last_origin_suffix
    {F pre : List Path} {source middle target : LTerm} {degree : Label} {site : Path}
    {edge reader oldReader first last : Path}
    (event : SelectedOldTurn F source degree pre middle target site)
    (selected : ∀p∈F,source.degreeAt p=some degree)
    (origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldReader first last) :
    ∃eventNode originalPosition originalNode,
      middle.subterm last=some eventNode ∧source.subterm originalPosition=some originalNode ∧
      BetaNodeHistoryPreimage event.labels last originalPosition ∧
      (eventNode.label=originalNode.label ∨∃preword marker,marker.MarksDegree degree ∧
        eventNode.label.letters=preword++marker::originalNode.label.letters) := by
  obtain ⟨_,eventNode,atEvent⟩ := origin.old_prerequisite event.redex
  obtain ⟨originalPosition,originalNode,atOriginal,trace⟩ :=
    event.labels.node_preimage_from_lookup atEvent
  obtain ⟨actual,atActual,suffix⟩ := event.beforeOld.node_label_suffix
    (DegreeAligned.initial source F) event.labels selected trace atEvent
  have equal := Option.some.inj (atActual.symm.trans atOriginal)
  subst actual
  exact ⟨eventNode,originalPosition,originalNode,atEvent,atOriginal,trace,suffix⟩

/-- Supplying a separately verified actual trace fixes the original coordinate
of the other-last edge. Only forward uniqueness is used. -/
theorem SelectedOldTurn.other_last_origin_suffix_at_trace
    {F pre : List Path} {source middle target : LTerm} {degree : Label} {site : Path}
    {edge reader oldReader first last originalPosition : Path}
    (event : SelectedOldTurn F source degree pre middle target site)
    (selected : ∀p∈F,source.degreeAt p=some degree)
    (origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldReader first last)
    (trace : BetaNodeHistoryPreimage event.labels last originalPosition) :
    ∃eventNode originalNode,middle.subterm last=some eventNode ∧
      source.subterm originalPosition=some originalNode ∧
      (eventNode.label=originalNode.label ∨∃preword marker,marker.MarksDegree degree ∧
        eventNode.label.letters=preword++marker::originalNode.label.letters) := by
  obtain ⟨eventNode,p,originalNode,atEvent,atOriginal,actual,suffix⟩ :=
    event.other_last_origin_suffix selected origin
  have same := actual.unique trace
  subst p
  exact ⟨eventNode,originalNode,atEvent,atOriginal,suffix⟩

#print axioms SelectedOldTurn.other_last_origin_suffix
#print axioms SelectedOldTurn.other_last_origin_suffix_at_trace
end Lamping.Lambda.Labelled
