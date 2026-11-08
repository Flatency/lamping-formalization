import Lamping.Lambda.AtomicProjection
import Lamping.Lambda.DerivationProjection
namespace Lamping.Lambda

theorem ParallelStep.paths_cast {F G : List Path} (eq : F = G) (h : ParallelStep F t u) :
    (eq ▸ h).paths = h.paths := by
  cases eq
  rfl

theorem ParallelHistory.cons_selection_cast {F G : List Path} (eq : F = G)
    (h : ParallelStep F t u) (tail : ParallelHistory u v) :
    ParallelHistory.cons (eq ▸ h) tail = ParallelHistory.cons h tail := by
  cases eq
  rfl

theorem ParallelStep.eq_of_paths (h k : ParallelStep F t u) (paths : h.paths = k.paths) : h = k := by
  apply h.ext_data k paths
  have hc := (Marked.completeOld_iff F t).mp h.complete
  have kc := (Marked.completeOld_iff F t).mp k.complete
  exact Marked.complete_unique ⟨hc.1.steps,hc.2⟩ ⟨kc.1.steps,kc.2⟩

theorem StepProjection.first_congr {h : ParallelStep F t u} {h' : ParallelStep G t u}
    (selection : F = G) (paths : h.paths = h'.paths) (row : StepProjection h σ τ last) :
    StepProjection h' σ τ last := by
  cases selection
  cases h.eq_of_paths h' paths
  exact row

theorem StepProjection.last_congr {last : ParallelStep F v w} {last' : ParallelStep G v w}
    (selection : F = G) (paths : last.paths = last'.paths) (row : StepProjection h σ τ last) :
    StepProjection h σ τ last' := by
  cases selection
  cases last.eq_of_paths last' paths
  exact row

theorem ParallelHistory.single_eq_of_selection_paths {h : ParallelStep F t u}
    (S : BetaAt t p u) (selection : F = [p]) (paths : h.paths = [p]) :
    ParallelHistory.single h = .single (singleContraction S) := by
  cases selection
  rw [h.eq_of_paths (singleContraction S) paths]

end Lamping.Lambda
