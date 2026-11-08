import Lamping.Lambda.WholeFamilyCopyUnitPlan
import Lamping.Lambda.CopyUnitPartitions

namespace Lamping.Lambda

private theorem partitioned_append {m t u v : Term}
    (pre : ParallelHistory m t) (rho : ParallelHistory t u)
    (sigma : ParallelHistory u v) :
    (wholeFamilyCopyUnitPlan (rho.append sigma)).Partitioned pre ↔
      (wholeFamilyCopyUnitPlan rho).Partitioned pre ∧
      (wholeFamilyCopyUnitPlan sigma).Partitioned (pre.append rho) := by
  induction rho with
  | nil =>
    simp only [ParallelHistory.append, wholeFamilyCopyUnitPlan,
      CopyUnitPlan.Partitioned, ParallelHistory.append_nil, true_and]
  | cons step tail ih =>
    simp only [ParallelHistory.append, wholeFamilyCopyUnitPlan, CopyUnitPlan.Partitioned]
    rw [ih]
    have samePrefix : (pre.append (.single step)).append tail =
        pre.append (.cons step tail) := by
      rw [ParallelHistory.append_assoc]
      rfl
    rw [samePrefix]
    constructor
    · rintro ⟨copies, disjoint, exactUnion, rest, later⟩
      exact ⟨⟨copies, disjoint, exactUnion, rest⟩, later⟩
    · rintro ⟨⟨copies, disjoint, exactUnion, rest⟩, later⟩
      exact ⟨copies, disjoint, exactUnion, rest, later⟩

private theorem single_partitioned {m t u : Term} {F : List Path}
    (pre : ParallelHistory m t) (step : ParallelStep F t u)
    (copies : CopySet pre F) (nonempty : F ≠ []) :
    (wholeFamilyCopyUnitPlan (.single step)).Partitioned pre := by
  change (∀ block ∈ [F], CopySet pre block ∧ block ≠ []) ∧
    [F].Pairwise (fun left right => ∀ p, p ∈ left → p ∈ right → False) ∧
    (∀ p, (∃ block ∈ [F], p ∈ block) ↔
      p ∈ F ∧ ∃ z, subtermAt t p = some z ∧ IsRedex z) ∧ True
  refine ⟨?_, ?_, ?_, trivial⟩
  · intro block selected
    cases List.mem_singleton.mp selected
    exact ⟨copies, nonempty⟩
  · simp
  · intro p
    constructor
    · rintro ⟨block, selected, member⟩
      cases List.mem_singleton.mp selected
      exact ⟨member, copies.1 p member⟩
    · rintro ⟨member, _valid⟩
      exact ⟨F, List.mem_singleton.mpr rfl, member⟩

/-- Each complete round is a strict partition with the actual selection as
its only block. Completeness supplies validity of every selected path. -/
theorem CompleteDerivation.wholeFamilyCopyUnitPlan_partitioned
    {m t : Term} {rho : ParallelHistory m t} (complete : CompleteDerivation rho) :
    (wholeFamilyCopyUnitPlan rho).Partitioned (.nil m) := by
  induction complete with
  | nil => trivial
  | @step v t pre F step previous whole ih =>
    have maximal := (previous.complete_step_iff_max_copies step).mp whole
    exact (partitioned_append (.nil m) pre (.single step)).mpr
      ⟨ih, single_partitioned pre step maximal.2.1 maximal.1⟩

/-- A complete, needed normalizing history realizes its own charged round
count and bounds every strict copy partition of every same-root NF history. -/
theorem CompleteDerivation.wholeFamilyCopyUnitPlan_minimal
    {m n : Term} {rho : ParallelHistory m n} (complete : CompleteDerivation rho)
    (needful : CallByNeedHistory rho) (_normal : BetaNF n) :
    (wholeFamilyCopyUnitPlan rho).Partitioned (.nil m) ∧
      ∀ {n' : Term} (sigma : ParallelHistory m n'), BetaNF n' →
        ∀ plan : CopyUnitPlan sigma, plan.Partitioned (.nil m) →
          (wholeFamilyCopyUnitPlan rho).units ≤ plan.units := by
  refine ⟨complete.wholeFamilyCopyUnitPlan_partitioned, ?_⟩
  intro n' sigma normal' plan partition
  rw [wholeFamilyCopyUnitPlan_units]
  exact complete.length_le_copy_partition_units needful sigma normal' plan partition

#print axioms Lamping.Lambda.CompleteDerivation.wholeFamilyCopyUnitPlan_partitioned
#print axioms Lamping.Lambda.CompleteDerivation.wholeFamilyCopyUnitPlan_minimal

end Lamping.Lambda
