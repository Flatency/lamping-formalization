import Lamping.Lambda.HistoryPreorder
import Lamping.Lambda.ProjectionSplits
namespace Lamping.Lambda

/-- Actual projection preserves the history prefix preorder. The witness
extension is projected through the first row's last vertical, and the given
second bottom is retained via generated-permutation coherence. -/
theorem HistoryPrefix.project {σ : ParallelHistory t v} {τ : ParallelHistory t w}
    (prefixOrder : HistoryPrefix σ τ) (step : ParallelStep F t u)
    (valid : ∀ p∈F,∃z,subtermAt t p=some z ∧ IsRedex z)
    {left : ParallelHistory u a} {right : ParallelHistory u b}
    {lastLeft : ParallelStep G v a} {lastRight : ParallelStep H w b}
    (first : StepProjection step σ left lastLeft) (second : StepProjection step τ right lastRight) :
    HistoryPrefix left right := by
  obtain ⟨extension,perm⟩ := prefixOrder
  obtain ⟨target,names,extension',last,row⟩ := StepProjection.exists_projection lastLeft extension
  have composed := first.append row
  obtain ⟨endpoint,equivalent⟩ := perm.projection_coherence step step (fun _ => Iff.rfl)
    valid composed second
  cases endpoint
  exact ⟨extension',equivalent⟩

theorem HistoryPrefix.project_beta {σ : ParallelHistory t v} {τ : ParallelHistory t w}
    (prefixOrder : HistoryPrefix σ τ) (R : BetaAt t p u)
    {left : ParallelHistory u a} {right : ParallelHistory u b}
    {lastLeft : ParallelStep G v a} {lastRight : ParallelStep H w b}
    (first : StepProjection (singleContraction R) σ left lastLeft)
    (second : StepProjection (singleContraction R) τ right lastRight) : HistoryPrefix left right :=
  prefixOrder.project (singleContraction R)
    (by intro q hq; cases List.mem_singleton.mp hq; exact R.redex) first second

end Lamping.Lambda
