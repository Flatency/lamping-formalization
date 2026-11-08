import Lamping.Lambda.UncreatedSourceHistory
import Lamping.Lambda.UniformOldNodeLabelSuffix
namespace Lamping.Lambda.Marked
open Labelled
/-- Safety of THIS final incoming label excludes every actual incoming
creation in a uniform OLD history. This is not safety of a reading chain. -/
theorem RelativeOldHistory.safe_incoming_uncreated
    {F ps : List Path} {m n : Marked} {d : Path →Option Label}
    {source target current : LTerm} {alpha : Label}
    {labels : Labelled.History ps source target} {p oldPosition : Path}
    (old : RelativeOldHistory F ps m n)
    (aligned : DegreeAligned d m source)
    (selected : ∀name∈F,d name=some alpha)
    (trace : BetaNodeHistoryPreimage labels p oldPosition)
    (lookup : target.subterm p=some current)
    (safe : current.label.OuterBarsSafe (fun x=>x≠alpha)) :
    UncreatedNodeHistoryPreimage labels p oldPosition := by
  induction trace generalizing m n with
  | nil => exact .nil _ _
  | @one site ps source middle target body argument beta head p mid oldPosition step remaining redex origin tailTrace ih =>
    cases old with
    | cons reduction member oldTail =>
      obtain ⟨name,chosen,residual⟩ := (mem_setResidualPositions _ _ _).mp member
      have atDegree := (aligned.trace_degree residual).trans (selected name chosen)
      simp only [LTerm.degreeAt,redex,Option.bind_some,LTerm.degree] at atDegree
      have sameAlpha := Option.some.inj atDegree
      cases sameAlpha
      have tailCert := ih oldTail (aligned.step reduction step) lookup
      obtain ⟨midNode,atMid,sameLabel⟩ := tailCert.source_label lookup
      have midSafe : midNode.label.OuterBarsSafe (fun x=>x≠alpha) := by
        rw [sameLabel];exact safe
      have uncreated : ¬BetaCreatedIncoming body site mid := by
        intro created
        exact (step.created_label_not_safe redex atMid created) midSafe
      exact .one (step:=step) redex origin uncreated tailCert

/-- Actual Source vertex ancestry follows for an alpha-safe incoming node.
No successful chain, chain-wide safety or endpoint iso is inferred. -/
theorem RelativeOldHistory.safe_incoming_source_history
    {F ps : List Path} {n : Marked} {source target current : LTerm}
    {alpha : Label} {labels : Labelled.History ps source target} {p oldPosition : Path}
    {vertex : SyntaxIncidence.Vertex target}
    (old : RelativeOldHistory F ps (mark F source.erase) n)
    (selected : ∀name∈F,source.degreeAt name=some alpha)
    (trace : BetaNodeHistoryPreimage labels p oldPosition)
    (lookup : target.subterm p=some current)
    (safe : current.label.OuterBarsSafe (fun x=>x≠alpha))
    (endpoint : SyntaxIncidence.Source target p vertex) :
    ∃original oldVertex,source.subterm oldPosition=some original ∧
      original.label=current.label ∧SyntaxIncidence.Source source oldPosition oldVertex ∧
      BetaVertexHistoryPreimage labels vertex oldVertex := by
  exact (old.safe_incoming_uncreated (DegreeAligned.initial source F) selected trace lookup safe).source_history lookup endpoint
#print axioms RelativeOldHistory.safe_incoming_uncreated
#print axioms RelativeOldHistory.safe_incoming_source_history
end Lamping.Lambda.Marked
