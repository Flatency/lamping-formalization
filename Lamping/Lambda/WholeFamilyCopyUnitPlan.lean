import Lamping.Lambda.CopyUnitComparison
import Lamping.Lambda.CompleteCopyCharacterization

namespace Lamping.Lambda

/-- Every raw PH batch contributes its literal full selection as one block.
This data definition has no completeness, ancestor or existence input. Empty
raw batches still yield an empty block; validity is proved only where true. -/
def wholeFamilyCopyUnitPlan {t u : Term} (rho : ParallelHistory t u) : CopyUnitPlan rho :=
  match rho with
  | .nil t => .nil t
  | @ParallelHistory.cons _ _ _ F step tail =>
      .cons [F] (wholeFamilyCopyUnitPlan tail)

theorem wholeFamilyCopyUnitPlan_units {t u : Term} (rho : ParallelHistory t u) :
    (wholeFamilyCopyUnitPlan rho).units=rho.length := by
  induction rho with
  | nil => rfl
  | cons step tail ih =>
    change 1+(wholeFamilyCopyUnitPlan tail).units=1+tail.length
    rw [ih]

/-- Exact prefix transport for the computed plan, with no completeness
assumption. The same ORIGINAL prehistory is extended by the actual rho. -/
theorem wholeFamilyCopyUnitPlan_valid_append {m t u v : Term}
    (pre : ParallelHistory m t) (rho : ParallelHistory t u) (sigma : ParallelHistory u v) :
    (wholeFamilyCopyUnitPlan (rho.append sigma)).Valid pre ↔
      (wholeFamilyCopyUnitPlan rho).Valid pre ∧
      (wholeFamilyCopyUnitPlan sigma).Valid (pre.append rho) := by
  induction rho with
  | nil =>
    simp only [ParallelHistory.append,wholeFamilyCopyUnitPlan,CopyUnitPlan.Valid,
      ParallelHistory.append_nil,true_and]
  | cons step tail ih =>
    simp only [ParallelHistory.append,wholeFamilyCopyUnitPlan,CopyUnitPlan.Valid]
    rw [ih]
    have samePrefix : (pre.append (.single step)).append tail=
        pre.append (.cons step tail) := by
      rw [ParallelHistory.append_assoc]
      rfl
    rw [samePrefix]
    constructor
    · rintro ⟨blocks,coverage,rest,later⟩
      exact ⟨⟨blocks,coverage,rest⟩,later⟩
    · rintro ⟨⟨blocks,coverage,rest⟩,later⟩
      exact ⟨blocks,coverage,rest,later⟩

private theorem whole_single_valid {m t u : Term} {F : List Path}
    (pre : ParallelHistory m t) (step : ParallelStep F t u)
    (copies : CopySet pre F) (nonempty : F≠[]) :
    (wholeFamilyCopyUnitPlan (.single step)).Valid pre := by
  change (∀ block∈[F],CopySet pre block ∧ block≠[]) ∧
    (∀ r : RedexOcc t,r.val∈F → ∃ block∈[F],r.val∈block) ∧ True
  constructor
  · intro block selected
    have same := List.mem_singleton.mp selected
    cases same
    exact ⟨copies,nonempty⟩
  · constructor
    · intro r selected
      exact ⟨F,List.mem_singleton.mpr rfl,selected⟩
    · trivial

/-- The existing AG5.4.8 PUBLIC theorem supplies the genuine CopySet at each
given complete prefix. No new common-ancestor or general completion theorem
is assumed or re-proved, and no semantic witness supplies plan data. -/
theorem CompleteDerivation.wholeFamilyCopyUnitPlan_valid
    {m t : Term} {rho : ParallelHistory m t} (complete : CompleteDerivation rho) :
    (wholeFamilyCopyUnitPlan rho).Valid (.nil m) := by
  induction complete with
  | nil => trivial
  | @step v t pre F step previous whole ih =>
    have maximal := (previous.complete_step_iff_max_copies step).mp whole
    apply (wholeFamilyCopyUnitPlan_valid_append (.nil m) pre (.single step)).mpr
    exact ⟨ih,whole_single_valid pre step maximal.2.1 maximal.1⟩

/-- Any normalizing complete competitor has a computed legal one-copy-unit
plan per whole-family round. Thus its round count bounds every complete
needed prefix at the SAME original root. No arbitrary PermEq FAM equality,
physical beta/administrative-step count or runtime-cost claim is used. -/
theorem CompleteDerivation.length_le_normalizing_complete_history
    {m t n : Term} {rho : ParallelHistory m t}
    (complete : CompleteDerivation rho) (needful : CallByNeedHistory rho)
    (sigma : ParallelHistory m n) (competitorComplete : CompleteDerivation sigma)
    (normal : BetaNF n) : rho.length≤sigma.length := by
  have bound := complete.length_le_copy_units needful sigma normal
    (wholeFamilyCopyUnitPlan sigma) competitorComplete.wholeFamilyCopyUnitPlan_valid
  rw [wholeFamilyCopyUnitPlan_units] at bound
  exact bound

#print axioms Lamping.Lambda.wholeFamilyCopyUnitPlan
#print axioms Lamping.Lambda.wholeFamilyCopyUnitPlan_units
#print axioms Lamping.Lambda.wholeFamilyCopyUnitPlan_valid_append
#print axioms Lamping.Lambda.CompleteDerivation.wholeFamilyCopyUnitPlan_valid
#print axioms Lamping.Lambda.CompleteDerivation.length_le_normalizing_complete_history

end Lamping.Lambda
