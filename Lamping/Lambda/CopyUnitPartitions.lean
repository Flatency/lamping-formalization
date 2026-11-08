import Lamping.Lambda.SingletonCopyUnitPlan

namespace Lamping.Lambda

private theorem prefix_positions_distinct (edge : Step) (ps : List Path)
    (distinct : ps.Nodup) : (ps.map (edge::·)).Nodup :=
  List.Pairwise.map _ (fun _ _ different same => different (List.cons.inj same).2) distinct

/-- Syntax occurrence enumeration does not duplicate literal syntax paths.
This is a tree property, with no assumption about family equality. -/
theorem syntax_positions_nodup (t : Term) : (positions t).Nodup := by
  induction t with
  | var => simp [positions]
  | lam b ih =>
    apply List.nodup_cons.mpr
    exact ⟨by simp, prefix_positions_distinct .body _ ih⟩
  | app f a hf ha =>
    apply List.nodup_cons.mpr
    constructor
    · simp
    · apply List.nodup_append.mpr
      refine ⟨prefix_positions_distinct .fn _ hf,prefix_positions_distinct .arg _ ha,?_⟩
      intro p hp q hq same
      obtain ⟨x,_hx,hx⟩ := List.mem_map.mp hp
      obtain ⟨y,_hy,hy⟩ := List.mem_map.mp hq
      cases hx.trans (same.trans hy.symm)

theorem syntax_redexPositions_nodup (t : Term) : (redexPositions t).Nodup := by
  exact List.Pairwise.filter _ (syntax_positions_nodup t)

/-- Distinctness is on the returned actual path values. Proof fields of the
computed RedexOcc subtype are not runtime equality tests. -/
theorem selectedRedexes_pairwise_paths (t : Term) (F : List Path) :
    (selectedRedexes t F).Pairwise (fun r s => r.val≠s.val) := by
  have input : (redexPositions t).attach.Pairwise (fun p q => p.val≠q.val) := by
    apply List.pairwise_map.mp
    simpa only [List.attach_map_subtype_val] using syntax_redexPositions_nodup t
  unfold selectedRedexes
  apply List.Pairwise.filterMap _ ?_ input
  intro p q different r picked s selected
  by_cases hp : p.val∈F
  · by_cases hq : q.val∈F
    · rw [if_pos hp] at picked
      rw [if_pos hq] at selected
      cases Option.some.inj picked
      cases Option.some.inj selected
      exact different
    · rw [if_neg hq] at selected
      cases selected
  · rw [if_neg hp] at picked
    cases picked

/-- A genuine admissible copy-unit partition schedule. Blocks are nonempty
CopySets at the actual ORIGINAL prefix, pairwise disjoint by path membership,
and their union is exactly the valid selected occurrences. Raw invalid or
repeated F names do not become cost events. This is stronger than Valid. -/
def CopyUnitPlan.Partitioned {m t u : Term} (pre : ParallelHistory m t)
    {rho : ParallelHistory t u} (plan : CopyUnitPlan rho) : Prop :=
  match plan with
  | .nil _ => True
  | @cons t _ _ F step _ blocks rest =>
      (∀ block∈blocks,CopySet pre block ∧ block≠[]) ∧
      blocks.Pairwise (fun left right => ∀ p,p∈left → p∈right → False) ∧
      (∀ p,(∃ block∈blocks,p∈block) ↔
        p∈F ∧ ∃ z,subtermAt t p=some z ∧ IsRedex z) ∧
      rest.Partitioned (pre.append (.single step))

/-- Every strict partition is a legitimate weak cover, without changing the
literal plan or its charged unit count. Only Prop fields are transported. -/
theorem CopyUnitPlan.Partitioned.valid {m t u : Term}
    {pre : ParallelHistory m t} {rho : ParallelHistory t u}
    {plan : CopyUnitPlan rho} (partition : plan.Partitioned pre) : plan.Valid pre := by
  revert pre
  induction plan with
  | nil => intro _pre _partition;trivial
  | @cons t u v F step tail blocks rest ih =>
    intro pre partition
    rcases partition with ⟨copies,_disjoint,exactUnion,later⟩
    refine ⟨copies,?_,ih later⟩
    intro r selected
    exact (exactUnion r.val).mpr ⟨selected,r.property⟩

private theorem singleton_blocks_disjoint (t : Term) (F : List Path) :
    ((selectedRedexes t F).map fun r => [r.val]).Pairwise
      (fun left right => ∀ p,p∈left → p∈right → False) := by
  apply List.Pairwise.map _ ?_ (selectedRedexes_pairwise_paths t F)
  intro r s different p left right
  exact different ((List.mem_singleton.mp left).symm.trans (List.mem_singleton.mp right))

/-- The previously computed singleton plan is a strict finite partition for
every actual competitor history, not merely a cover. It is not reconstructed
from an existential semantic representative or a family-equality decision. -/
theorem singletonCopyUnitPlan_partitioned {m t u : Term}
    (pre : ParallelHistory m t) (rho : ParallelHistory t u) :
    (singletonCopyUnitPlan rho).Partitioned pre := by
  induction rho with
  | nil => trivial
  | @cons t u v F step tail ih =>
    change (∀ block∈(selectedRedexes t F).map (fun r => [r.val]),CopySet pre block ∧ block≠[]) ∧
      ((selectedRedexes t F).map fun r => [r.val]).Pairwise
        (fun left right => ∀ p,p∈left → p∈right → False) ∧
      (∀ p,(∃ block∈(selectedRedexes t F).map (fun r => [r.val]),p∈block) ↔
        p∈F ∧ ∃ z,subtermAt t p=some z ∧ IsRedex z) ∧
      (singletonCopyUnitPlan tail).Partitioned (pre.append (.single step))
    refine ⟨?_,singleton_blocks_disjoint t F,?_,ih (pre.append (.single step))⟩
    · intro block member
      obtain ⟨r,_selected,same⟩ := List.mem_map.mp member
      cases same
      exact ⟨singleton_copySet pre r,by intro impossible;cases impossible⟩
    · intro p
      constructor
      · rintro ⟨block,inBlocks,member⟩
        obtain ⟨r,selected,same⟩ := List.mem_map.mp inBlocks
        cases same
        have samePath := List.mem_singleton.mp member
        constructor
        · rw [samePath]
          exact (mem_selectedRedexes t F r).mp selected
        · simpa only [samePath] using r.property
      · rintro ⟨selected,redex⟩
        let r : RedexOcc t := ⟨p,redex⟩
        refine ⟨[p],?_,List.mem_singleton.mpr rfl⟩
        exact List.mem_map.mpr ⟨r,(mem_selectedRedexes t F r).mpr selected,rfl⟩

theorem finite_copy_partition_exists {m t u : Term}
    (pre : ParallelHistory m t) (rho : ParallelHistory t u) :
    ∃ plan : CopyUnitPlan rho,plan.Partitioned pre :=
  ⟨singletonCopyUnitPlan rho,singletonCopyUnitPlan_partitioned pre rho⟩

/-- The AG copies-unit lower bound now ranges over EVERY genuine finite
partition schedule of EVERY same-root NF competitor. Competitors need not be
complete, needed, atomic or standard. The analysis Needed property is not a
field of an executable graph strategy. -/
theorem CompleteDerivation.length_le_copy_partition_units
    {m t n : Term} {rho : ParallelHistory m t}
    (complete : CompleteDerivation rho) (needful : CallByNeedHistory rho)
    (sigma : ParallelHistory m n) (normal : BetaNF n)
    (plan : CopyUnitPlan sigma) (partition : plan.Partitioned (.nil m)) :
    rho.length≤plan.units :=
  complete.length_le_copy_units needful sigma normal plan partition.valid

#print axioms Lamping.Lambda.syntax_positions_nodup
#print axioms Lamping.Lambda.syntax_redexPositions_nodup
#print axioms Lamping.Lambda.selectedRedexes_pairwise_paths
#print axioms Lamping.Lambda.CopyUnitPlan.Partitioned
#print axioms Lamping.Lambda.CopyUnitPlan.Partitioned.valid
#print axioms Lamping.Lambda.singletonCopyUnitPlan_partitioned
#print axioms Lamping.Lambda.finite_copy_partition_exists
#print axioms Lamping.Lambda.CompleteDerivation.length_le_copy_partition_units

end Lamping.Lambda
