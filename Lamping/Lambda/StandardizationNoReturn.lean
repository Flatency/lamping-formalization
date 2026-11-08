import Lamping.Lambda.StandardizationProtection
import Lamping.Lambda.StandardPrefixes
import Lamping.Lambda.ProjectionFamilies
namespace Lamping.Lambda
/-- For an ordinary history every actual selected contraction is its step's
LO, so no-return excludes any genuinely used earlier source occurrence. -/
theorem DoesNotReturnLeft.no_used_left {ρ : ParallelHistory t u} {r : RedexOcc t}
    (noReturn : DoesNotReturnLeft r ρ) (atomic : Atomic ρ)
    (s : RedexOcc t) (before : LeftOf s.val r.val) : ¬UsedSource ρ s := by
  rintro ⟨v,w,F,pre,step,suffix,q,eq,selected,residual⟩
  have whole : Atomic (pre.append (.cons step suffix)) := by rw [←eq]; exact atomic
  have tail := whole.split_append.2
  cases tail with
  | cons head rest =>
    have same : q=⟨_,head.redex⟩ := Subtype.ext (List.mem_singleton.mp selected)
    subst q
    exact noReturn s before pre (singleContraction head) suffix eq _ (leftmost_singleton _) residual

/-- Fixed-source no-return is preserved by genuine permutation of an ordinary
history. This does not assert that standardness itself is permutation invariant. -/
theorem DoesNotReturnLeft.permutation {ρ σ : ParallelHistory t u} {r : RedexOcc t}
    (noReturn : DoesNotReturnLeft r ρ) (atomic : Atomic ρ) (perm : PermEq ρ σ) :
    DoesNotReturnLeft r σ := by
  apply DoesNotReturnLeft.of_right r
  intro s before
  have right : RightHistory s.val ρ := ρ.right_of_no_used s (by
    intro q prior
    apply noReturn.no_used_left atomic q
    rcases prior with same | earlier
    · rw [same]; exact before
    · exact earlier.trans before)
  exact RightHistory.permutation s right perm

/-- Keep an actual ordinary prefix while replacing its suffix by a true
permutation that may have an extra final extension. Standardness of the new
suffix is separately required; no PermEq-implies-Standard rule is introduced. -/
theorem Standard.replace_suffix_extension {pre : ParallelHistory m t} (prefixAtomic : Atomic pre)
    {old : ParallelHistory t u} (oldAtomic : Atomic old) (standard : Standard (pre.append old))
    {next : ParallelHistory t v} (nextStandard : Standard next) (extra : ParallelHistory v u)
    (perm : PermEq old (next.append extra)) : Standard (pre.append next) := by
  induction prefixAtomic with
  | nil => exact nextStandard
  | @cons source path mid target rest head restAtomic ih =>
    cases standard with
    | cons _ r lo noReturn restStandard =>
      have equivalent := PermEq.prepend (ParallelHistory.cons (singleContraction head) rest) perm
      have extended := noReturn.permutation ((Atomic.cons head restAtomic).append oldAtomic) equivalent
      have short : DoesNotReturnLeft r ((ParallelHistory.cons (singleContraction head) rest).append next) := by
        rw [←ParallelHistory.append_assoc] at extended
        exact extended.prefix
      exact .cons (singleContraction head) r lo short (ih oldAtomic restStandard nextStandard perm)
end Lamping.Lambda
namespace Lamping.Lambda
/-- No genuinely used earlier source redex suffices for no-return, even
without any atomicity assumption on the candidate history. -/
theorem DoesNotReturnLeft.of_no_used {ρ : ParallelHistory t u} (r : RedexOcc t)
    (unused : ∀ s : RedexOcc t, LeftOf s.val r.val → ¬UsedSource ρ s) : DoesNotReturnLeft r ρ := by
  intro s before v w F pre step suffix eq q lo residual
  exact unused s before ⟨v,w,F,pre,step,suffix,q,eq,lo.1,residual⟩
end Lamping.Lambda
