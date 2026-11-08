import Lamping.Lambda.OrdinarySubstitution
import Lamping.Lambda.DisjointRowPaths
import Lamping.Lambda.FunctionRowPaths
namespace Lamping.Lambda

/-- Reconstruct a genuine ordinary substituted region row. Its projected
 program is identified with the supplied old program after substitution by
 ordered paths, not by endpoint coincidence or a postulated row. -/
theorem StepProjection.substitute_region (R : BetaAt t p u)
    {original : ParallelHistory t v} {projected : ParallelHistory u w}
    (row : StepProjection (singleContraction R) original projected last)
    (ho : Atomic original) (hp : Atomic projected)
    (region : ExtractionRegion p site) (inside : Internal site original) (σ : Nat → Term) :
    ∃ (F : List Path) (vertical : ParallelStep F (subst σ v) (subst σ w)),
      StepProjection (singleContraction (R.subst σ)) (ho.substitute σ) (hp.substitute σ) vertical := by
  obtain ⟨z,K,bottom,vertical,hb,newRow⟩ := (ho.substitute_atomic σ).region_projection
    (singleContraction (R.subst σ)) rfl ⟨p,(R.subst σ).redex⟩ rfl region (ho.substitute_internal inside σ)
  have samePaths : bottom.derivation.paths=(hp.substitute σ).derivation.paths := by
    rw [hp.substitute_paths]
    rcases region with apart | function
    · have sourcePaths := row.disjoint_paths R ho hp apart inside
      have targetPaths := newRow.disjoint_paths (R.subst σ) (ho.substitute_atomic σ) hb apart
        (ho.substitute_internal inside σ)
      exact targetPaths.symm.trans ((ho.substitute_paths σ).trans sourcePaths)
    · have functionInside : Internal (p++[.fn]) original := by simpa only [function] using inside
      obtain ⟨oldProgram,oldSource,oldTarget⟩ := row.function_paths R ho hp functionInside
      obtain ⟨newProgram,newSource,newTarget⟩ := newRow.function_paths (R.subst σ)
        (ho.substitute_atomic σ) hb (ho.substitute_internal functionInside σ)
      have programs : newProgram=oldProgram := by
        apply mapped_prefix_paths_injective (p++[.fn,.body])
        rw [←newSource,ho.substitute_paths,oldSource]
      exact newTarget.trans (by rw [programs,oldTarget])
  have endpoint := bottom.derivation.valid.deterministic (by
    have valid := (hp.substitute σ).derivation.valid
    rw [←samePaths] at valid
    exact valid)
  cases endpoint
  have histories := hb.paths_injective (hp.substitute_atomic σ) samePaths
  cases histories
  exact ⟨K,vertical,newRow⟩

end Lamping.Lambda
