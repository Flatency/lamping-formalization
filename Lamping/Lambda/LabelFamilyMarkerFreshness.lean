import Lamping.Lambda.LabelParallelOuterBars
import Lamping.Lambda.LabelFamilyDegreeEquivalence
import Lamping.Lambda.LabelFirstCandidateOrder
import Lamping.Lambda.CompleteFamiliesExhaustion

namespace Lamping.Lambda.Labelled

private theorem safe_of_unused_families {t u : Term}
    (program : ParallelHistory t u) {original source target : LTerm} {forbidden : Label}
    (sourceErase : source.erase=t) (targetErase : target.erase=u)
    (prior : ParallelHistory original.erase t)
    (priorLabels : History prior.derivation.paths original source)
    (labels : History program.derivation.paths source target)
    (safe : source.OuterBarsSafe (fun payload=>payload≠forbidden))
    (unused : ∀ point : RedexWithHistory original.erase,FamilyUsedAt prior program point →
      degreeAlong original point.history.derivation.paths point.redex.val≠some forbidden) :
    target.OuterBarsSafe (fun payload=>payload≠forbidden) := by
  induction program generalizing source target with
  | nil => cases labels;exact safe
  | @cons t middle finish F step tail ih =>
    change History (step.paths++tail.derivation.paths) source target at labels
    obtain ⟨next,firstLabels,restLabels⟩ := labels.split
    obtain ⟨known,knownLabels,nextErase⟩ := lift_history step.derivation.valid source sourceErase
    have same : next=known := firstLabels.deterministic knownLabels
    subst next
    cases sourceErase
    cases nextErase
    have selected (path : Path) (member : path∈F) (degree : Label)
        (atDegree : source.degreeAt path=some degree) : degree≠forbidden := by
      obtain ⟨beta,body,argument,lookup⟩ := LTerm.degreeAt_redex atDegree
      let redex : RedexOcc source.erase := ⟨path,.app (.lam body.erase) argument.erase,by
        rw [←LTerm.erase_subterm,lookup];rfl,True.intro⟩
      let point : RedexWithHistory original.erase := ⟨source.erase,prior,redex⟩
      have used : FamilyUsedAt prior (.cons step tail) point := .head member (.refl _)
      have excluded := unused point used
      change degreeAlong original prior.derivation.paths path≠some forbidden at excluded
      rw [degreeAlong_witness priorLabels,atDegree] at excluded
      intro equal
      exact excluded (congrArg some equal)
    have nextSafe := step.outerBarsSafe firstLabels safe selected
    have nextPriorLabels : History (prior.append (.single step)).derivation.paths original known := by
      simpa only [ParallelHistory.derivation_append,ParallelHistory.single_derivation,
        ParallelStep.derivation,Derivation.append] using priorLabels.append firstLabels
    exact ih rfl targetErase (prior.append (.single step)) nextPriorLabels restLabels nextSafe
      (fun point used=>unused point (.tail used))

/-- Before the next current redex is fired, no existing outer edge marker
contains its degree as an immediate over/under payload. The history must
already be a complete-family derivation from the SAME original INIT.
The proof uses actual OLD residual degrees and the proved no-future-family
theorem; it supplies no completion of an arbitrary history. -/
theorem complete_prefix_outer_bars_fresh {original current : LTerm}
    (initial : INIT original)
    (program : ParallelHistory original.erase current.erase)
    (complete : CompleteDerivation program)
    (labels : History program.derivation.paths original current)
    (redex : RedexOcc current.erase) (atDegree : current.degreeAt redex.val=some degree) :
    current.OuterBarsSafe (fun payload=>payload≠degree) := by
  let currentPoint : RedexWithHistory original.erase := ⟨current.erase,program,redex⟩
  have noFuture : ¬FamilyUsed program currentPoint := by
    simpa only [ParallelHistory.append_nil] using complete.no_future_family (.nil _) redex
  have currentDegree : degreeAlong original program.derivation.paths redex.val=some degree := by
    rw [degreeAlong_witness labels]
    exact atDegree
  have unused (point : RedexWithHistory original.erase) (used : FamilyUsed program point) :
      degreeAlong original point.history.derivation.paths point.redex.val≠some degree := by
    intro same
    have related : FamilyEq point currentPoint :=
      (family_iff_degree original initial point currentPoint).mpr (same.trans currentDegree.symm)
    exact noFuture ((FamilyUsed.closed program) related used)
  exact safe_of_unused_families program rfl rfl (.nil _) (.nil _) labels
    (initial.outerBarsSafe _) unused

end Lamping.Lambda.Labelled
