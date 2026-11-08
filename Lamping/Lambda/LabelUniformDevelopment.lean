import Lamping.Lambda.LabelCreatedClassification
namespace Lamping.Lambda.Marked
open Labelled

/-- Across the exact OLD schedule, a label without the common fired
degree's marker must originate in the initial labelled source. Intermediate
sources may already contain that marker; no stepwise freshness is assumed. -/
theorem RelativeOldHistory.marker_free_label_origin {F ps : List Path} {m n : Marked}
    (old : RelativeOldHistory F ps m n) {d : Path →Option Label}
    {source target current : LTerm} {edge : Path} {degree : Label}
    (aligned : DegreeAligned d m source) (labels : Labelled.History ps source target)
    (selected : ∀ path∈F,d path=some degree)
    (lookup : target.subterm edge=some current)
    (safe : current.label.OuterBarsSafe (fun payload=>payload≠degree)) :
    current.label∈source.labels := by
  induction old generalizing source target with
  | nil => cases labels;exact LTerm.label_mem_of_subterm lookup
  | @cons path _ _ _ _ reduction member tail ih =>
    cases labels with
    | cons turn remaining =>
      have inherited := ih (aligned.step reduction turn) remaining lookup
      obtain ⟨oldEdge,oldNode,atOld,labelEq⟩ := LTerm.label_mem_located _ inherited
      obtain ⟨name,chosen,residual⟩ := (mem_setResidualPositions _ _ _).mp member
      have atDegree := (aligned.trace_degree residual).trans (selected name chosen)
      obtain ⟨beta,body,argument,redex⟩ := LTerm.degreeAt_redex atDegree
      have notCreated : ¬BetaCreatedIncoming body path oldEdge := by
        intro created
        apply turn.created_label_not_safe redex atOld created
        rw [labelEq];exact safe
      have oldMember := turn.uncreated_label_mem redex atOld notCreated
      rw [labelEq] at oldMember
      exact oldMember
end Lamping.Lambda.Marked

namespace Lamping.Lambda
open Labelled

/-- The actual complete development of a uniformly labelled selection
introduces no new marker-free label. The source need not be INIT. -/
theorem ParallelStep.marker_free_label_origin {source target current : LTerm}
    {F : List Path} {edge : Path} {degree : Label}
    (step : ParallelStep F source.erase target.erase)
    (labels : History step.paths source target)
    (selected : ∀ path∈F,source.degreeAt path=some degree)
    (lookup : target.subterm edge=some current)
    (safe : current.label.OuterBarsSafe (fun payload=>payload≠degree)) :
    current.label∈source.labels :=
  step.complete.1.marker_free_label_origin (DegreeAligned.initial source F) labels selected lookup safe

/-- If the common marker is initially fresh, target labels are old exactly
when they remain marker-free. This concerns the given whole OLD schedule,
not just the first or last ordinary beta event. -/
theorem ParallelStep.label_mem_iff_marker_free {source target current : LTerm}
    {F : List Path} {edge : Path} {degree : Label}
    (step : ParallelStep F source.erase target.erase)
    (labels : History step.paths source target)
    (selected : ∀ path∈F,source.degreeAt path=some degree)
    (sourceSafe : source.OuterBarsSafe (fun payload=>payload≠degree))
    (lookup : target.subterm edge=some current) :
    current.label∈source.labels ↔current.label.OuterBarsSafe (fun payload=>payload≠degree) :=
  ⟨fun member=>(LTerm.outerBarsSafe_iff _ _).mp sourceSafe _ member,
    step.marker_free_label_origin labels selected lookup⟩

end Lamping.Lambda
