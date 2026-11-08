import Lamping.Lambda.ProjectionSplits
import Lamping.Lambda.ExtractionInternal
import Lamping.Lambda.AtomicRowExistence
namespace Lamping.Lambda

/-- Restrict a source rule (ii)/(iii) row at an arbitrary nonempty ordinary
 bottom prefix. The restricted extraction and the remaining row retain the
 prescribed actual schedule; this does not append a suffix to extraction. -/
theorem StepProjection.extraction_prefix (R : BetaAt t p u)
    {σ : ParallelHistory t v} (pre : ParallelHistory u mid)
    (post : ParallelHistory mid w) {last : ParallelStep G v w}
    (row : StepProjection (singleContraction R) σ (pre.append post) last)
    (ha : Atomic σ) (hb : Atomic pre) (hc : Atomic post)
    (region : ExtractionRegion p site) (inside : Internal site σ)
    (positive : 0 < pre.length) :
    ∃ (x : Term) (K : List Path) (topPre : ParallelHistory t x)
      (topPost : ParallelHistory x v) (vertical : ParallelStep K x mid)
      (hpre : Atomic topPre) (_hpost : Atomic topPost),
      σ = topPre.append topPost ∧ Internal site topPre ∧ Internal site topPost ∧
      StepProjection (singleContraction R) topPre pre vertical ∧
      StepProjection vertical topPost post last ∧
      ExtractionStep (.of (.cons (singleContraction R) pre) (.cons R hb)) (.of topPre hpre) := by
  obtain ⟨x, K, topPre, topPost, vertical, hp, hq, he, row1, row2⟩ :=
    row.split_bottom pre post ha hb hc
  have internalParts := (Internal.append_iff topPre topPost).mp (he ▸ inside)
  have pos : 0 < topPre.length := by rw [← row1.length]; exact positive
  refine ⟨x, K, topPre, topPost, vertical, hp, hq, he,
    internalParts.1, internalParts.2, row1, row2, ?_⟩
  rcases region with hd | hf
  · exact ExtractionStep.disjoint (.nil t) (.nil t) R topPre hp pre hb vertical row1
      pos site hd internalParts.1
  · subst site
    exact ExtractionStep.functionPart (.nil t) (.nil t) R topPre hp pre hb vertical row1
      pos internalParts.1

end Lamping.Lambda
