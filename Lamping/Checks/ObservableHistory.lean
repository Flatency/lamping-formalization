import Lamping.Lambda.ObservableHistory
import Lamping.Lambda.SingleContraction

namespace Lamping.Checks.ObservableHistory
open Lambda

private abbrev delta : Term := .lam (.app (.var 0) (.var 0))
private abbrev omega : Term := .app delta delta
private def contraction : BetaAt omega [] omega :=
  ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩

/-- Silence before and after a real self-reduction cannot delete that
reduction merely because the endpoints coincide. -/
theorem silent_boundaries_preserve_self_reduction :
    let raw : ParallelHistory omega omega :=
      .cons (ParallelStep.empty omega)
        (.cons (singleContraction contraction) (.single (ParallelStep.empty omega)))
    ∃ observed : ParallelHistory omega omega,
      ParallelHistory.Observable observed ∧ raw.derivation=observed.derivation ∧
      PermEq raw observed ∧ observed.derivation.paths=[[]] ∧ observed≠.nil omega := by
  intro raw
  obtain ⟨observed,positive,same,permutation⟩ := raw.exists_observable
  have paths : observed.derivation.paths=[[]] := by rw [←same]; rfl
  refine ⟨observed,positive,same,permutation,paths,?_⟩
  intro empty
  rw [empty] at paths
  cases paths

/-- An empty old selection is silent even on a reducible source. -/
example : (ParallelStep.empty omega).paths=[] ∧ IsRedex omega := ⟨rfl,True.intro⟩

#print axioms ParallelStep.empty_paths
#print axioms ParallelHistory.exists_observable
#print axioms silent_boundaries_preserve_self_reduction
end Lamping.Checks.ObservableHistory
