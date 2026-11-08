import Lamping.Lambda.NodeLabelSuffixOrigins
import Lamping.Lambda.UniformOldChainPreimages
namespace Lamping.Lambda.Marked
open Labelled

/-- Literal suffix ancestry along the SAME actual OLD history. No safety
hypothesis is imposed on the source or any intermediate annotation. -/
theorem RelativeOldHistory.node_label_suffix
    {F ps : List Path} {m n : Marked} (old : RelativeOldHistory F ps m n)
    {d : Path →Option Label} {source target current : LTerm} {alpha : Label}
    {p oldPosition : Path}
    (aligned : DegreeAligned d m source) (labels : Labelled.History ps source target)
    (selected : ∀name∈F,d name=some alpha)
    (trace : BetaNodeHistoryPreimage labels p oldPosition)
    (lookup : target.subterm p=some current) :
    ∃original,source.subterm oldPosition=some original ∧
      (current.label=original.label ∨∃pre marker,marker.MarksDegree alpha ∧
        current.label.letters=pre++marker::original.label.letters) := by
  induction trace generalizing m n with
  | nil => exact ⟨current,lookup,Or.inl rfl⟩
  | @one site ps source middle target body argument beta head p mid oldPosition step remaining redex origin tailTrace ih =>
    cases old with
    | @cons _ _ _ _ _ reduction member oldTail =>
        obtain ⟨name,chosen,residual⟩ := (mem_setResidualPositions _ _ _).mp member
        have atDegree := (aligned.trace_degree residual).trans (selected name chosen)
        simp only [LTerm.degreeAt,redex,Option.bind_some,LTerm.degree] at atDegree
        have sameAlpha := Option.some.inj atDegree
        cases sameAlpha
        obtain ⟨mid,atMid,later⟩ := ih oldTail (aligned.step reduction step) lookup
        obtain ⟨original,atOriginal,earlier⟩ := step.beta_node_label_suffix redex origin atMid
        refine ⟨original,atOriginal,?_⟩
        rcases earlier with same |⟨pre,marker,marks,equal⟩
        · rcases later with sameLater |⟨post,other,otherMarks,otherEqual⟩
          · exact Or.inl (sameLater.trans same)
          · exact Or.inr ⟨post,other,otherMarks,by rw [otherEqual,same]⟩
        · rcases later with sameLater |⟨post,other,otherMarks,otherEqual⟩
          · exact Or.inr ⟨pre,marker,marks,by rw [sameLater,equal]⟩
          · refine Or.inr ⟨post++other::pre,marker,marks,?_⟩
            rw [otherEqual,equal]
            simp only [List.append_assoc,List.cons_append]
#print axioms RelativeOldHistory.node_label_suffix

/-- Word reversal of the complete original-node suffix. -/
theorem RelativeOldHistory.node_label_suffix_reverse
    {F ps : List Path} {m n : Marked} (old : RelativeOldHistory F ps m n)
    {d : Path →Option Label} {source target current : LTerm} {alpha : Label}
    {p oldPosition : Path}
    (aligned : DegreeAligned d m source) (labels : Labelled.History ps source target)
    (selected : ∀name∈F,d name=some alpha)
    (trace : BetaNodeHistoryPreimage labels p oldPosition)
    (lookup : target.subterm p=some current) :
    ∃original,source.subterm oldPosition=some original ∧
      (current.label=original.label ∨∃marker post,marker.MarksDegree alpha ∧
        current.label.readLetters false=original.label.readLetters false++marker::post) := by
  obtain ⟨original,atOriginal,same |⟨pre,marker,marks,equal⟩⟩ :=
    old.node_label_suffix aligned labels selected trace lookup
  · exact ⟨original,atOriginal,Or.inl same⟩
  · refine ⟨original,atOriginal,Or.inr ⟨marker,pre.reverse,marks,?_⟩⟩
    change current.label.letters.reverse=original.label.letters.reverse++marker::pre.reverse
    rw [equal]
    simp only [List.reverse_append,List.reverse_cons,List.singleton_append,List.append_assoc]

/-- Only the original source must be safe. Every intermediate source is
allowed to contain alpha markers. The coordinate remains THIS trace's origin. -/
theorem RelativeOldHistory.node_last_marker
    {F ps : List Path} {m n : Marked} (old : RelativeOldHistory F ps m n)
    {d : Path →Option Label} {source target current : LTerm} {alpha : Label}
    {p oldPosition : Path}
    (aligned : DegreeAligned d m source) (labels : Labelled.History ps source target)
    (selected : ∀name∈F,d name=some alpha)
    (trace : BetaNodeHistoryPreimage labels p oldPosition)
    (lookup : target.subterm p=some current)
    (sourceSafe : source.OuterBarsSafe (fun payload=>payload≠alpha))
    (marked : ¬current.label.OuterBarsSafe (fun payload=>payload≠alpha)) :
    ∃original pre marker,source.subterm oldPosition=some original ∧
      original.label.OuterBarsSafe (fun payload=>payload≠alpha) ∧marker.MarksDegree alpha ∧
      current.label.letters=pre++marker::original.label.letters ∧
      current.label.readLetters false=original.label.readLetters false++marker::pre.reverse := by
  obtain ⟨original,atOriginal,same |⟨pre,marker,marks,equal⟩⟩ :=
    old.node_label_suffix aligned labels selected trace lookup
  · have safe := (LTerm.outerBarsSafe_iff _ _).mp sourceSafe original.label (LTerm.label_mem_of_subterm atOriginal)
    exact False.elim (marked (same ▸ safe))
  · have safe := (LTerm.outerBarsSafe_iff _ _).mp sourceSafe original.label (LTerm.label_mem_of_subterm atOriginal)
    refine ⟨original,pre,marker,atOriginal,safe,marks,equal,?_⟩
    change current.label.letters.reverse=original.label.letters.reverse++marker::pre.reverse
    rw [equal]
    simp only [List.reverse_append,List.reverse_cons,List.singleton_append,List.append_assoc]
#print axioms RelativeOldHistory.node_label_suffix_reverse
#print axioms RelativeOldHistory.node_last_marker
end Lamping.Lambda.Marked
