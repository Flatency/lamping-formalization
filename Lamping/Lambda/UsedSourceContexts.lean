import Lamping.Lambda.StandardizationNoReturn
namespace Lamping.Lambda
/-- Actual use in a nonempty history is either its selected head or an
actual later use of a real residual through that head. -/
theorem UsedSource.cons_iff (first : ParallelStep F t u) (tail : ParallelHistory u v) (r : RedexOcc t) :
    UsedSource (.cons first tail) r ↔ r.val∈F ∨ ∃ s : RedexOcc u, first.derivation.Residual r s ∧ UsedSource tail s := by
  constructor
  · rintro ⟨a,b,G,pre,step,suffix,q,eq,selected,residual⟩
    cases pre with
    | nil =>
      simp only [ParallelHistory.append] at eq
      cases eq
      have same := (Derivation.residual_nil r q).mp residual
      subst q
      exact Or.inl selected
    | cons head rest =>
      simp only [ParallelHistory.append] at eq
      cases eq
      change (first.derivation.append rest.derivation).Residual r q at residual
      obtain ⟨s,firstResidual,restResidual⟩ := (Derivation.residual_append _ _ r q).mp residual
      exact Or.inr ⟨s,firstResidual,⟨a,b,G,rest,step,suffix,q,rfl,selected,restResidual⟩⟩
  · rintro (selected | ⟨s,residual,used⟩)
    · exact ⟨t,u,F,.nil _,first,tail,r,rfl,selected,(Derivation.residual_nil r r).mpr rfl⟩
    · exact used.prepend (.single first) r (by simpa only [ParallelHistory.single_derivation] using residual)

/-- Inclusion of genuinely selected old sources is preserved under a shared
actual prefix, despite possibly different final endpoints. -/
theorem UsedSource.common_prefix (pre : ParallelHistory m t)
    {old : ParallelHistory t u} {next : ParallelHistory t v}
    (inclusion : ∀ r : RedexOcc t, UsedSource next r → UsedSource old r)
    (r : RedexOcc m) (used : UsedSource (pre.append next) r) : UsedSource (pre.append old) r := by
  induction pre with
  | nil => exact inclusion r used
  | cons first rest ih =>
    rcases (UsedSource.cons_iff first (rest.append next) r).mp used with selected | ⟨s,residual,later⟩
    · exact (UsedSource.cons_iff first (rest.append old) r).mpr (Or.inl selected)
    · exact (UsedSource.cons_iff first (rest.append old) r).mpr (Or.inr ⟨s,residual,ih inclusion s later⟩)

/-- Source-prefix no-return follows from inclusion of actual used old names,
while standardness of the replacement suffix is proved independently. -/
theorem Standard.replace_suffix_used {pre : ParallelHistory m t} (prefixAtomic : Atomic pre)
    {old : ParallelHistory t u} (oldAtomic : Atomic old) (standard : Standard (pre.append old))
    {next : ParallelHistory t v} (nextStandard : Standard next)
    (inclusion : ∀ r : RedexOcc t, UsedSource next r → UsedSource old r) : Standard (pre.append next) := by
  induction prefixAtomic with
  | nil => exact nextStandard
  | @cons source path mid target rest head restAtomic ih =>
    cases standard with
    | cons _ r lo noReturn restStandard =>
      have shortened : DoesNotReturnLeft r ((ParallelHistory.cons (singleContraction head) rest).append next) := by
        apply DoesNotReturnLeft.of_no_used
        intro s before used
        apply noReturn.no_used_left ((Atomic.cons head restAtomic).append oldAtomic) s before
        exact UsedSource.common_prefix (ParallelHistory.cons (singleContraction head) rest) inclusion s used
      exact .cons (singleContraction head) r lo shortened (ih oldAtomic restStandard nextStandard inclusion)
end Lamping.Lambda

