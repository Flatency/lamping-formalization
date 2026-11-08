import Lamping.Lambda.ArgumentLiftSplits
import Lamping.Lambda.ArgumentResidualScope
namespace Lamping.Lambda

/-- A nonempty specified-copy history identifies its bound-variable leaf.
 Distinct argument instances are disjoint actual variable occurrences. -/
theorem ArgumentLift.copy_occurrence_unique (R : BetaAt t p u)
    {σ : ParallelHistory u v} {original : ParallelHistory t w} {original' : ParallelHistory t w'}
    (lift : ArgumentLift R σ original) (lift' : ArgumentLift R σ original')
    (ha : Atomic σ) (positive : 0 < σ.length) : lift.occurrence = lift'.occurrence := by
  classical
  have bodies : lift.body = lift'.body := by
    have shape := Option.some.inj (lift.redex.symm.trans lift'.redex)
    exact Term.lam.inj (Term.app.inj shape).1
  cases ha with
  | nil => change 0 < 0 at positive; omega
  | @cons u q a v tail S hs =>
    have first : q ∈ (ParallelHistory.cons (singleContraction S) tail).derivation.paths := by
      change q ∈ q :: _
      exact List.mem_cons_self
    obtain ⟨a, ha⟩ := lift.copy_internal q first
    obtain ⟨b, hb⟩ := lift'.copy_internal q first
    by_cases equal : lift.occurrence = lift'.occurrence
    · exact equal
    apply False.elim
    have different := equal
    have other : ArgumentOccurrence lift.body lift'.occurrence := by
      rw [bodies]
      exact lift'.isVariable
    have disjoint := lift.isVariable.context_disjoint other different p
    rcases List.prefix_or_prefix_of_prefix
      (show p ++ lift.occurrence <+: q from ⟨a, ha.symm⟩)
      (show p ++ lift'.occurrence <+: q from ⟨b, hb.symm⟩) with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact disjoint.1 ⟨r, hr.symm⟩
    · exact disjoint.2 ⟨r, hr.symm⟩

/-- Two rule-(iv) presentations at the same deleted redex and with the same
 nonempty chosen-copy schedule have the same actual original history. -/
theorem ArgumentLift.original_run_unique (R : BetaAt t p u)
    {σ : ParallelHistory u v} {original : ParallelHistory t w} {original' : ParallelHistory t w'}
    (lift : ArgumentLift R σ original) (lift' : ArgumentLift R σ original')
    (ha : Atomic σ) (ho : Atomic original) (ho' : Atomic original') (positive : 0 < σ.length) :
    ExtractionRun.of original ho = ExtractionRun.of original' ho' := by
  have occurrence := lift.copy_occurrence_unique R lift' ha positive
  have copied := lift.copy_paths.symm.trans lift'.copy_paths
  rw [occurrence] at copied
  have locals := mapped_prefix_paths_injective _ copied
  apply ExtractionRun.ext_paths
  change original.derivation.paths = original'.derivation.paths
  rw [lift.original_paths, lift'.original_paths, locals]

end Lamping.Lambda
