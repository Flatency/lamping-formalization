import Lamping.Lambda.ArgumentResidualScope
import Lamping.Lambda.OrdinarySplits
import Lamping.Lambda.ResidualOrigins
namespace Lamping.Lambda

theorem ArgumentLift.head_residual (R : BetaAt t p u)
    (S : BetaAt u s v) (A : BetaAt t a x)
    (tail : ParallelHistory v w) (originalTail : ParallelHistory x w')
    (lift : ArgumentLift R (.cons (singleContraction S) tail)
      (.cons (singleContraction A) originalTail)) :
    (singleContraction R).derivation.Residual ⟨a, A.redex⟩ ⟨s, S.redex⟩ := by
  cases localPaths : lift.localPaths with
  | nil =>
    have copied := lift.copy_paths
    rw [localPaths] at copied
    change s :: tail.derivation.paths = [] at copied
    cases copied
  | cons q rest =>
    have copied : s = (p ++ lift.occurrence) ++ q := by
      have h := lift.copy_paths
      rw [localPaths] at h
      change s :: tail.derivation.paths = ((p ++ lift.occurrence) ++ q) :: _ at h
      exact (List.cons.inj h).1
    have original : a = (p ++ [.arg]) ++ q := by
      have h := lift.original_paths
      rw [localPaths] at h
      change a :: originalTail.derivation.paths = ((p ++ [.arg]) ++ q) :: _ at h
      exact (List.cons.inj h).1
    exact (R.argument_residual_iff lift.redex ⟨a, A.redex⟩ original ⟨s, S.redex⟩).mpr
      ⟨lift.occurrence, lift.isVariable, copied⟩

/-- A specified one-contraction argument copy is a real residual of the
 mirrored original argument contraction, including arbitrary binder depth. -/
theorem ArgumentLift.singleton_residual (R : BetaAt t p u)
    (S : BetaAt u s v) (S' : BetaAt t s' v')
    (lift : ArgumentLift R (.single (singleContraction S)) (.single (singleContraction S'))) :
    (singleContraction R).derivation.Residual ⟨s', S'.redex⟩ ⟨s, S.redex⟩ := by
  have len : lift.localPaths.length = 1 := by
    have h := congrArg List.length lift.copy_paths
    change 1 = (List.map _ lift.localPaths).length at h
    simpa only [List.length_map] using h.symm
  obtain ⟨q, hq⟩ := List.length_eq_one_iff.mp len
  have copied : s = (p ++ lift.occurrence) ++ q := by
    have h := lift.copy_paths
    change [s] = _ at h
    simpa only [hq, List.map_cons, List.map_nil, List.cons.injEq, and_true] using h
  have original : s' = (p ++ [.arg]) ++ q := by
    have h := lift.original_paths
    change [s'] = _ at h
    simpa only [hq, List.map_cons, List.map_nil, List.cons.injEq, and_true] using h
  exact (R.argument_residual_iff lift.redex ⟨s', S'.redex⟩ original ⟨s, S.redex⟩).mpr
    ⟨lift.occurrence, lift.isVariable, copied⟩

/-- In the singleton (i,iv) overlap both actual deletion targets agree.
 Equality uses unique old-redex origins rather than endpoint coincidence. -/
theorem residual_argument_target_unique (R : BetaAt t p u) (S : BetaAt u s v)
    (A : BetaAt t a x) (S' : BetaAt t s' v')
    (residual : (singleContraction R).derivation.Residual ⟨a, A.redex⟩ ⟨s, S.redex⟩)
    (lift : ArgumentLift R (.single (singleContraction S)) (.single (singleContraction S'))) :
    ExtractionRun.of (.single (singleContraction A)) (.single A) =
      ExtractionRun.of (.single (singleContraction S')) (.single S') := by
  have origin := (singleContraction R).derivation.residual_unique_source
    ⟨a, A.redex⟩ ⟨s', S'.redex⟩ ⟨s, S.redex⟩ residual (lift.singleton_residual R S S')
  apply ExtractionRun.ext_paths
  have path : a = s' := congrArg Subtype.val origin
  change [a] = [s']
  rw [path]

end Lamping.Lambda
