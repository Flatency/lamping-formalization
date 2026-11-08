import Lamping.Lambda.CopyUnitComparison

namespace Lamping.Lambda

/-- A current redex is its own ancestor, with the actual nil extension at its
given ORIGINAL-root history. This proof constructs no runtime representative. -/
theorem singleton_copySet {m t : Term} (pre : ParallelHistory m t) (r : RedexOcc t) :
    CopySet pre [r.val] := by
  constructor
  · intro p member
    have same := List.mem_singleton.mp member
    simpa only [same] using r.property
  · refine ⟨⟨t,pre,r⟩,.nil t,?_,?_⟩
    · simpa only [ParallelHistory.append_nil] using PermEq.refl pre
    · intro s
      change s.val ∈ [r.val] ↔ (Derivation.nil t).Residual r s
      rw [Derivation.residual_nil]
      constructor
      · intro member
        exact (Subtype.ext (List.mem_singleton.mp member)).symm
      · intro same
        cases same
        exact List.mem_singleton.mpr rfl

/-- Pure syntax enumeration gives one singleton block per actual selected
valid occurrence. A duplicate name in F creates no extra block. -/
def singletonCopyUnitPlan {t u : Term} (rho : ParallelHistory t u) : CopyUnitPlan rho :=
  match rho with
  | .nil t => .nil t
  | @ParallelHistory.cons t _u v F step tail =>
      .cons ((selectedRedexes t F).map fun r => [r.val]) (singletonCopyUnitPlan tail)

theorem singletonCopyUnitPlan_valid {m t u : Term}
    (pre : ParallelHistory m t) (rho : ParallelHistory t u) :
    (singletonCopyUnitPlan rho).Valid pre := by
  induction rho with
  | nil => trivial
  | @cons t u v F step tail ih =>
    change (∀ block∈(selectedRedexes t F).map (fun r => [r.val]),
        CopySet pre block ∧ block≠[]) ∧
      (∀ r : RedexOcc t,r.val∈F →
        ∃ block∈(selectedRedexes t F).map (fun r => [r.val]),r.val∈block) ∧
      (singletonCopyUnitPlan tail).Valid (pre.append (.single step))
    constructor
    · intro block member
      obtain ⟨r,_selected,same⟩ := List.mem_map.mp member
      cases same
      exact ⟨singleton_copySet pre r,by intro impossible;cases impossible⟩
    · constructor
      · intro r selected
        refine ⟨[r.val],?_,List.mem_singleton.mpr rfl⟩
        exact List.mem_map.mpr ⟨r,(mem_selectedRedexes t F r).mpr selected,rfl⟩
      · exact ih (pre.append (.single step))

/-- Count actual selected syntax occurrences, not parallel batches or graph
events. The same finite enumerator supplies both this data and the plan. -/
def selectedOccurrenceCount {t u : Term} (rho : ParallelHistory t u) : Nat :=
  match rho with
  | .nil _ => 0
  | @ParallelHistory.cons t _ _ F _ tail =>
      (selectedRedexes t F).length+selectedOccurrenceCount tail

theorem singletonCopyUnitPlan_units {t u : Term} (rho : ParallelHistory t u) :
    (singletonCopyUnitPlan rho).units=selectedOccurrenceCount rho := by
  induction rho with
  | nil => rfl
  | cons step tail ih =>
    change ((selectedRedexes _ _).map (fun r => [r.val])).length+
        (singletonCopyUnitPlan tail).units=_
    rw [List.length_map,ih]
    rfl

/-- No valid-plan existence hypothesis remains: the competitor's plan is the
computed singleton plan above. This is an occurrence-count corollary of copy
unit comparison, not a claim that a parallel batch costs one copy unit. -/
theorem CompleteDerivation.length_le_selectedOccurrenceCount
    {m t n : Term} {rho : ParallelHistory m t}
    (complete : CompleteDerivation rho) (needful : CallByNeedHistory rho)
    (sigma : ParallelHistory m n) (normal : BetaNF n) :
    rho.length≤selectedOccurrenceCount sigma := by
  have bound := complete.length_le_copy_units needful sigma normal
    (singletonCopyUnitPlan sigma) (singletonCopyUnitPlan_valid (.nil m) sigma)
  rw [singletonCopyUnitPlan_units] at bound
  exact bound

#print axioms Lamping.Lambda.singleton_copySet
#print axioms Lamping.Lambda.singletonCopyUnitPlan
#print axioms Lamping.Lambda.singletonCopyUnitPlan_valid
#print axioms Lamping.Lambda.selectedOccurrenceCount
#print axioms Lamping.Lambda.singletonCopyUnitPlan_units
#print axioms Lamping.Lambda.CompleteDerivation.length_le_selectedOccurrenceCount

end Lamping.Lambda
