import Lamping.Lambda.RootResidualSet
namespace Lamping.Lambda

theorem ParallelStep.ext_data (h k : ParallelStep F t u)
    (paths : h.paths = k.paths) (target : h.markedTarget = k.markedTarget) : h = k := by
  cases h
  cases k
  cases paths
  cases target
  rfl

theorem ParallelStep.eq_single_contraction (h : ParallelStep [p] t u) (r : RedexOcc t) (hp : r.val = p) :
    ∃ hb : BetaAt t p u, h = singleContraction hb := by
  have hpaths := h.singleton_paths r hp
  have hv := h.derivation.valid
  change BetaHistory h.paths t u at hv
  rw [hpaths] at hv
  have hb : BetaAt t p u := by cases hv with | cons h hs => cases hs; exact h
  refine ⟨hb, ?_⟩
  apply h.ext_data (singleContraction hb) hpaths
  have hh := (Marked.completeOld_iff [p] t).mp h.complete
  have hk := (Marked.completeOld_iff [p] t).mp (singleContraction hb).complete
  exact Marked.complete_unique ⟨hh.1.steps, hh.2⟩ ⟨hk.1.steps, hk.2⟩

end Lamping.Lambda
