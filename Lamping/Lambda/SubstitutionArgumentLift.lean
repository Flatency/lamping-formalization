import Lamping.Lambda.OrdinarySubstitution
import Lamping.Lambda.ArgumentPullback
namespace Lamping.Lambda

theorem liftSubN_bound (σ : Nat → Term) (n i : Nat) (bound : i<n) :
    liftSubN n σ i=.var i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change rename Nat.succ (liftSubN n σ i)=.var (i+1)
      rw [ih i (by omega)]
      rfl

/-- Substitution outside a redex's binder preserves every specified instance
 of that binder, including instances below further lambdas. -/
theorem ArgumentOccurrence.substitute (h : ArgumentOccurrence b occurrence) (σ : Nat → Term) :
    ArgumentOccurrence (subst (liftSub σ) b) occurrence := by
  have result := subtermAt_subst h (liftSub σ)
  unfold ArgumentOccurrence
  simpa only [liftSubN_shift,subst,liftSubN_bound σ (binderDepth occurrence+1)
    (binderDepth occurrence) (by omega)] using result

noncomputable def ArgumentLift.substitute {R : BetaAt t p u}
    (lift : ArgumentLift R copy original) (hc : Atomic copy) (ho : Atomic original)
    (σ : Nat → Term) :
    ArgumentLift (R.subst σ) (hc.substitute σ) (ho.substitute σ) where
  body := subst (liftSub (liftSubN (binderDepth p) σ)) lift.body
  argument := subst (liftSubN (binderDepth p) σ) lift.argument
  redex := subtermAt_subst lift.redex σ
  occurrence := lift.occurrence
  isVariable := lift.isVariable.substitute (liftSubN (binderDepth p) σ)
  localPaths := lift.localPaths
  copy_paths := by rw [hc.substitute_paths]; exact lift.copy_paths
  original_paths := by rw [ho.substitute_paths]; exact lift.original_paths
  parallelization := StepProjection.exists_projection (singleContraction (R.subst σ)) (ho.substitute σ)

end Lamping.Lambda
