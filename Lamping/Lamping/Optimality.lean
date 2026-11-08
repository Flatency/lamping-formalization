import Lamping.Lambda.Optimality
import Lamping.Lamping.ComputedFamilyHistoryReplay
import Lamping.Lamping.NeededGraphFamilyOptimality

namespace Lamping.AG.Readback
open Lambda Lambda.Labelled

private theorem historyBetas {paths : List Path} {source target : Term}
    (history : BetaHistory paths source target) : Betas source target := by
  induction history with
  | nil t => exact .refl t
  | cons head _tail ih => exact .cons head.beta ih

/-- The actual initialized graph evaluator reads back an ordinary beta reduct
of its input in beta-normal form. -/
theorem normalizeNeededGraph_reduces (term : Term)
    (closed : Closed term) (normalizable : HasNF term) :
    let result := (normalizeNeededGraph term closed normalizable).val
    Betas term result.term ∧ BetaNF result.term := by
  obtain ⟨normal, _current, _schemas, _raw, prior, _trace, _projection, _same,
    _complete, _needful, erased⟩ := normalizeNeededGraph_spec term closed normalizable
  have reduction := historyBetas prior.derivation.valid
  rw [erase_initLabels, erased] at reduction
  exact ⟨reduction, normal⟩

end Lamping.AG.Readback
