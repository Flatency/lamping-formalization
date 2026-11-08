import Lamping.Lambda.SubstitutionArgumentLift
import Lamping.Lambda.SubstitutionRegionProjection
import Lamping.Lambda.ValidParallelSubstitution
namespace Lamping.Lambda

private theorem single_paths (R : BetaAt t p u) : (singleContraction R).derivation.paths=[p] := rfl

private theorem step_subst_paths (σ : Nat → Term) {r s : ExtractionRun m}
    {r' s' : ExtractionRun (Lambda.subst σ m)} (step : ExtractionStep r' s')
    (source : r'.history.derivation.paths=r.history.derivation.paths)
    (target : s'.history.derivation.paths=s.history.derivation.paths) :
    ExtractionStep (r.subst σ) (s.subst σ) := by
  have er : r.subst σ=r' := by
    apply ExtractionRun.ext_paths
    rw [ExtractionRun.subst_paths]
    exact source.symm
  have es : s.subst σ=s' := by
    apply ExtractionRun.ext_paths
    rw [ExtractionRun.subst_paths]
    exact target.symm
  rw [er,es]
  exact step

/-- Capture-avoiding substitution preserves each original extraction
 generator. Ordinary paths remain fixed; region rows are reconstructed from
 their geometry, and argument rules retain the specified variable instance. -/
theorem ExtractionStep.subst (step : ExtractionStep r s) (σ : Nat → Term) :
    ExtractionStep (r.subst σ) (s.subst σ) := by
  cases step with
  | residual pre ha R S A old =>
    have traces := (singleContraction R).substitution_trace_eq
      (singleContraction (R.subst σ)) rfl ⟨_,A.redex⟩
    have transported : (singleContraction (R.subst σ)).derivation.Residual
        ⟨_,(A.subst σ).redex⟩ ⟨_,(S.subst σ).redex⟩ := by
      rw [ParallelStep.residual_iff] at old ⊢
      rw [←traces]
      exact old
    have built := ExtractionStep.residual (ha.substitute σ) (ha.substitute_atomic σ)
        (R.subst σ) (S.subst σ) (A.subst σ) transported
    apply step_subst_paths σ built <;>
      simp only [ExtractionRun.of,ParallelHistory.derivation_append,
        Derivation.append,Atomic.substitute_paths,ParallelHistory.single_derivation,single_paths]
  | disjoint pre ha R original ho projected hp last row positive site apart inside =>
    obtain ⟨K,vertical,newRow⟩ := row.substitute_region R ho hp (.inl apart) inside σ
    have built := ExtractionStep.disjoint (ha.substitute σ) (ha.substitute_atomic σ) (R.subst σ)
        _ (ho.substitute_atomic σ) _ (hp.substitute_atomic σ) vertical newRow
        (by rw [ho.substitute_length]; exact positive) site apart (ho.substitute_internal inside σ)
    apply step_subst_paths σ built <;>
      simp only [ExtractionRun.of,ParallelHistory.derivation_append,
        Derivation.append,Atomic.substitute_paths,ParallelHistory.single_derivation,single_paths]
  | functionPart pre ha R original ho projected hp last row positive inside =>
    obtain ⟨K,vertical,newRow⟩ := row.substitute_region R ho hp (.inr rfl) inside σ
    have built := ExtractionStep.functionPart (ha.substitute σ) (ha.substitute_atomic σ) (R.subst σ)
        _ (ho.substitute_atomic σ) _ (hp.substitute_atomic σ) vertical newRow
        (by rw [ho.substitute_length]; exact positive) (ho.substitute_internal inside σ)
    apply step_subst_paths σ built <;>
      simp only [ExtractionRun.of,ParallelHistory.derivation_append,
        Derivation.append,Atomic.substitute_paths,ParallelHistory.single_derivation,single_paths]
  | argumentPart pre ha R copy hc original ho positive lift =>
    have built := ExtractionStep.argumentPart (ha.substitute σ) (ha.substitute_atomic σ) (R.subst σ)
        _ (hc.substitute_atomic σ) _ (ho.substitute_atomic σ)
        (by rw [hc.substitute_length]; exact positive) (lift.substitute hc ho σ)
    apply step_subst_paths σ built <;>
      simp only [ExtractionRun.of,ParallelHistory.derivation_append,
        Derivation.append,Atomic.substitute_paths,ParallelHistory.single_derivation,single_paths]

theorem Extraction.subst (steps : Extraction r s) (σ : Nat → Term) :
    Extraction (r.subst σ) (s.subst σ) := by
  induction steps with
  | refl => exact .refl _
  | cons head rest ih => exact .cons (head.subst σ) ih

theorem ExtractionNormal.subst_reflect (normal : ExtractionNormal (r.subst σ)) : ExtractionNormal r := by
  rintro ⟨target,step⟩
  exact normal ⟨target.subst σ,step.subst σ⟩

end Lamping.Lambda
