import Lamping.Lambda.LabelOuterBarProvenance
import Lamping.Lambda.LabelResiduals

namespace Lamping.Lambda.Marked
open Labelled

/-- Only actual selected residuals can fire in an OLD development. Their
degrees are read from the SAME transported old-name alignment, so a policy
on source selected degrees suffices for every real contraction in the schedule. -/
theorem RelativeOldHistory.outerBarsSafe {F ps : List Path} {m n : Marked}
    (old : RelativeOldHistory F ps m n) {d : Path →Option Label}
    {source target : LTerm} {allowed : Label →Prop}
    (aligned : DegreeAligned d m source) (labels : Labelled.History ps source target)
    (safe : source.OuterBarsSafe allowed)
    (selected : ∀ path∈F,∀ degree,d path=some degree →allowed degree) :
    target.OuterBarsSafe allowed := by
  induction old generalizing source target with
  | nil => cases labels;exact safe
  | cons reduction member tail ih =>
    cases labels with
    | cons turn remaining =>
      obtain ⟨name,chosen,residual⟩ := (mem_setResidualPositions _ _ _).mp member
      have atDegree := aligned.trace_degree residual
      have degreeAllowed (degree) (actual : _=some degree) : allowed degree :=
        selected name chosen degree (atDegree.symm.trans actual)
      exact ih (aligned.step reduction turn) remaining (turn.outerBarsSafe safe degreeAllowed)
end Lamping.Lambda.Marked

namespace Lamping.Lambda
open Labelled

/-- A complete parallel step introduces only outer markers of degrees of
its actually selected OLD source redexes. The labels follow its exact given
schedule; no family completeness, INIT or alternate schedule is substituted. -/
theorem ParallelStep.outerBarsSafe {source target : LTerm} {F : List Path}
    (step : ParallelStep F source.erase target.erase)
    (labels : History step.paths source target) {allowed : Label →Prop}
    (safe : source.OuterBarsSafe allowed)
    (selected : ∀ path∈F,∀ degree,source.degreeAt path=some degree →allowed degree) :
    target.OuterBarsSafe allowed :=
  step.complete.1.outerBarsSafe (DegreeAligned.initial source F) labels safe selected

end Lamping.Lambda
