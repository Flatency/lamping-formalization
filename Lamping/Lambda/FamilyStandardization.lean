import Lamping.Lambda.FamilyStandardizationPull
namespace Lamping.Lambda

theorem ParallelHistory.extract_minimal_supported (ρ : ParallelHistory t u)
    (used : ∃ r : RedexOcc t, UsedSource ρ r) (pre : ParallelHistory m t) :
    ∃ (s : RedexOcc t) (z : Term) (head : BetaAt t s.val z) (tail : ParallelHistory z u),
      PermEq ρ ((ParallelHistory.single (singleContraction head)).append tail) ∧
      tail.length=ρ.length ∧ HistoryCost.ListLt tail.costs ρ.costs ∧
      (∀ r : RedexOcc t, LeftOf r.val s.val → RightHistory r.val ρ) ∧
      ∀ a, FamilyUsedAt pre ((ParallelHistory.single (singleContraction head)).append tail) a →
        FamilyUsedAt pre ρ a := by
  obtain ⟨s,sUsed,minimal⟩ := UsedSource.leftmost_exists ρ used
  have protection : ∀ r : RedexOcc t, LeftOf r.val s.val → RightHistory r.val ρ := by
    intro r before
    apply ρ.right_of_no_used r
    intro q prior
    apply minimal q
    rcases prior with same | left
    · rw [same]; exact before
    · exact left.trans before
  rcases ρ.right_or_kills_left s with safe | ⟨r,prior,usedR,_⟩
  · exact False.elim (safe.not_used_self s sUsed)
  · have same : r=s := by
      rcases prior with same | left
      · exact Subtype.ext same
      · exact False.elim (minimal r left usedR.used)
    subst r
    obtain ⟨v,w,F,before,step,suffix,q,eq,right,selected,residual⟩ := usedR
    have fixed := (before.derivation.left_fixed s right.paths_right q).mp residual
    have selectedS : s.val∈F := by rw [←fixed]; exact selected
    obtain ⟨z,head,tail,perm,length,less,support⟩ := right.pull_selected_supported s rfl step selectedS suffix pre
    refine ⟨s,z,head,tail,?_,?_,?_,protection,?_⟩
    · rw [eq]; exact perm
    · rw [eq]; exact length
    · rw [eq]; exact less
    · intro a used; rw [eq]; exact support a used

/-- The same genuine reverse-cost construction as general standardization,
strengthened with directional support at every global history prefix. -/
theorem atomic_standardization_exists_supported (ρ : ParallelHistory t u) (pre : ParallelHistory m t) :
    ∃ σ : ParallelHistory t u, Atomic σ ∧ Standard σ ∧ PermEq ρ σ ∧
      ∀ a, FamilyUsedAt pre σ a → FamilyUsedAt pre ρ a := by
  classical
  have main (n : Nat) : ∀ c : HistoryCost n, ∀ {t u : Term} (ρ : ParallelHistory t u)
      (length : ρ.length=n), HistoryCost.ofList n ρ.costs (ρ.costs_length.trans length)=c →
      ∀ {m : Term} (pre : ParallelHistory m t),
      ∃ σ : ParallelHistory t u, Atomic σ ∧ Standard σ ∧ PermEq ρ σ ∧
        ∀ a, FamilyUsedAt pre σ a → FamilyUsedAt pre ρ a := by
    intro c
    apply (HistoryCost.wellFounded n).induction c
    intro c ih t u ρ length cost m pre
    by_cases used : ∃ r : RedexOcc t, UsedSource ρ r
    · obtain ⟨s,z,head,tail,pull,sameLength,less,protection,support⟩ := ρ.extract_minimal_supported used pre
      have tailLength : tail.length=n := sameLength.trans length
      let next := HistoryCost.ofList n tail.costs (tail.costs_length.trans tailLength)
      have decrease : HistoryCost.Lt n next c := by
        rw [←cost]
        exact less.toCost n (tail.costs_length.trans tailLength) (ρ.costs_length.trans length)
      obtain ⟨σ,atomic,standard,permuted,tailSupport⟩ :=
        ih next decrease tail tailLength rfl (pre.append (.single (singleContraction head)))
      let result : ParallelHistory t u := (ParallelHistory.single (singleContraction head)).append σ
      have equivalence : PermEq ρ result := .trans pull (.prepend (.single (singleContraction head)) permuted)
      refine ⟨result,.cons head atomic,?_,equivalence,?_⟩
      · apply Standard.cons (singleContraction head) s (leftmost_singleton s)
        · apply DoesNotReturnLeft.of_right s
          intro r before
          exact RightHistory.permutation r (protection r before) equivalence
        · exact standard
      · intro a event
        change FamilyUsedAt pre (.cons (singleContraction head) σ) a at event
        apply support a
        cases event with
        | head selected family => exact .head selected family
        | tail later => exact .tail (tailSupport a later)
    · have noneUsed : ∀ r : RedexOcc t, ¬UsedSource ρ r := fun r hr => used ⟨r,hr⟩
      obtain ⟨same,perm⟩ := ρ.no_used noneUsed
      subst u
      refine ⟨.nil t,.nil t,.nil t,perm,?_⟩
      intro a event; cases event
  exact main ρ.length _ ρ rfl rfl pre

/-- The standard ordinary representative can be chosen to use only families
already present in the actual input history. Arbitrary PermEq representatives
need not have this property. -/
theorem atomic_standardization_exists_relative (ρ : ParallelHistory t u) :
    ∃ σ : ParallelHistory t u, Atomic σ ∧ Standard σ ∧ PermEq ρ σ ∧
      RelativeFamilies σ (FamilyUsed ρ) := by
  obtain ⟨σ,atomic,standard,perm,support⟩ := atomic_standardization_exists_supported ρ (.nil t)
  exact ⟨σ,atomic,standard,perm,support⟩

end Lamping.Lambda
