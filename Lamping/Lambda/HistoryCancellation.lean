import Lamping.Lambda.PermutationCancellation
import Lamping.Lambda.StandardizationGeneral
namespace Lamping.Lambda

/-- Cancellation along an actual ordinary prefix, by its successive beta
heads. The suffixes may have arbitrary parallel groupings. -/
theorem PermEq.cancel_atomic_prefix {pre : ParallelHistory m t} (ordinary : Atomic pre)
    {a b : ParallelHistory t u} (perm : PermEq (pre.append a) (pre.append b)) : PermEq a b := by
  induction ordinary with
  | nil => exact perm
  | cons R tail ih => exact ih (perm.cancel_beta_head R)

/-- General left cancellation for the generated permutation relation.
The common prefix is genuinely standardized to an ordinary representative;
no extraction confluence or family theorem is used. -/
theorem PermEq.cancel_prefix (pre : ParallelHistory m t) {a b : ParallelHistory t u}
    (perm : PermEq (pre.append a) (pre.append b)) : PermEq a b := by
  obtain ⟨ordinary,atomic,_,same⟩ := atomic_standardization_exists pre
  have joined : PermEq (ordinary.append a) (ordinary.append b) :=
    (same.symm.append a).trans (perm.trans (same.append b))
  exact joined.cancel_atomic_prefix atomic

theorem Copy.cancel_prefix (pre : ParallelHistory m t) (a b : RedexWithHistory t)
    (copy : Copy ⟨a.target,pre.append a.history,a.redex⟩
      ⟨b.target,pre.append b.history,b.redex⟩) : Copy a b := by
  obtain ⟨extension,perm,residual⟩ := copy
  refine ⟨extension,?_,residual⟩
  rw [ParallelHistory.append_assoc] at perm
  exact perm.cancel_prefix pre

end Lamping.Lambda
