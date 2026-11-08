import Lamping.Lambda.CompleteFamilyRounds
import Lamping.Lambda.MaximalCopies

namespace Lamping.Lambda

/-- Literal finite grouping of each actual batch. It contains only path lists;
semantic validity is a separate proposition, not an answer-producing oracle. -/
inductive CopyUnitPlan : {t u : Term} → ParallelHistory t u → Type
  | nil (t : Term) : CopyUnitPlan (.nil t)
  | cons {t u v : Term} {F : List Path} {step : ParallelStep F t u}
      {tail : ParallelHistory u v} (blocks : List (List Path))
      (rest : CopyUnitPlan tail) : CopyUnitPlan (.cons step tail)

/-- Every charged block is an actual nonempty copy set at the SAME original
prefix. Every selected valid occurrence is covered. No family conclusion,
neededness, normal form or desired unit bound is stored in this predicate. -/
def CopyUnitPlan.Valid {m t u : Term} (pre : ParallelHistory m t)
    {rho : ParallelHistory t u} (plan : CopyUnitPlan rho) : Prop :=
  match plan with
  | .nil _ => True
  | @cons t _ _ F step _ blocks rest =>
      (∀ block∈blocks,CopySet pre block ∧ block≠[]) ∧
      (∀ r : RedexOcc t,r.val∈F → ∃ block∈blocks,r.val∈block) ∧
      rest.Valid (pre.append (.single step))

def CopyUnitPlan.units {t u : Term} {rho : ParallelHistory t u}
    (plan : CopyUnitPlan rho) : Nat :=
  match plan with
  | .nil _ => 0
  | .cons blocks rest => blocks.length+rest.units

/-- A block's representative is computed by the existing syntax traversal.
No representative is extracted from CopySet's ancestor existential. -/
def copyUnitFamily {m t : Term} (pre : ParallelHistory m t)
    (block : List Path) : Option (FamilyClass m) :=
  (firstSelectedRedex t block).map fun r => familyClassOf ⟨t,pre,r⟩

def CopyUnitPlan.familiesAt {m t u : Term} (pre : ParallelHistory m t)
    {rho : ParallelHistory t u} (plan : CopyUnitPlan rho) : List (FamilyClass m) :=
  match plan with
  | .nil _ => []
  | @cons _ _ _ _ step _ blocks rest =>
      blocks.filterMap (copyUnitFamily pre)++rest.familiesAt (pre.append (.single step))

theorem CopySet.firstSelectedRedex_some {m t : Term}
    {pre : ParallelHistory m t} {block : List Path}
    (copies : CopySet pre block) (nonempty : block≠[]) :
    ∃ r : RedexOcc t,firstSelectedRedex t block=some r := by
  cases chosen : firstSelectedRedex t block with
  | some r => exact ⟨r,rfl⟩
  | none =>
    have empty : selectedRedexes t block=[] := List.head?_eq_none_iff.mp chosen
    cases block with
    | nil => exact False.elim (nonempty rfl)
    | cons p ps =>
      let r : RedexOcc t := ⟨p,copies.1 p List.mem_cons_self⟩
      have member := (mem_selectedRedexes t (p::ps) r).mpr List.mem_cons_self
      rw [empty] at member
      cases member

/-- One genuine nonempty copy unit contributes exactly one historical family,
even when it contains many selected occurrences or duplicate path names. -/
theorem CopySet.copyUnitFamily_member {m t : Term}
    {pre : ParallelHistory m t} {block : List Path}
    (copies : CopySet pre block) (nonempty : block≠[])
    (r : RedexOcc t) (member : r.val∈block) :
    copyUnitFamily pre block=some (familyClassOf ⟨t,pre,r⟩) := by
  obtain ⟨chosen,selected⟩ := copies.firstSelectedRedex_some nonempty
  have inBlock := firstSelectedRedex_selected t block chosen selected
  have same := (familyClassOf_eq_iff ⟨t,pre,chosen⟩ ⟨t,pre,r⟩).mpr
    (copies.same_family chosen r inBlock member)
  simp only [copyUnitFamily,selected,Option.map_some,same]

theorem CopyUnitPlan.familyUsed_mem {m t u : Term}
    (pre : ParallelHistory m t) {rho : ParallelHistory t u}
    (plan : CopyUnitPlan rho) (valid : plan.Valid pre)
    (a : RedexWithHistory m) (used : FamilyUsedAt pre rho a) :
    familyClassOf a∈plan.familiesAt pre := by
  revert pre
  induction plan with
  | nil => intro pre _valid used;cases used
  | @cons t u v F step tail blocks rest ih =>
    intro pre valid used
    rcases valid with ⟨blocksValid,covered,tailValid⟩
    cases used with
    | head selected family =>
      obtain ⟨block,inBlocks,inBlock⟩ := covered _ selected
      have fact := blocksValid block inBlocks
      have picked := fact.1.copyUnitFamily_member fact.2 _ inBlock
      have same := (familyClassOf_eq_iff _ a).mpr family
      apply List.mem_append.mpr
      apply Or.inl
      apply List.mem_filterMap.mpr
      exact ⟨block,inBlocks,by rw [picked,same]⟩
    | tail later => exact List.mem_append.mpr (.inr (ih _ tailValid later))

private theorem filterMap_length_bound {A B : Type} (f : A → Option B) (xs : List A) :
    (xs.filterMap f).length≤xs.length := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    cases hx : f x with
    | none => simpa only [List.filterMap_cons,hx,List.length_cons] using
        Nat.le_trans ih (Nat.le_succ xs.length)
    | some y => simpa only [List.filterMap_cons,hx,List.length_cons] using Nat.succ_le_succ ih

theorem CopyUnitPlan.familiesAt_length_le {m t u : Term}
    (pre : ParallelHistory m t) {rho : ParallelHistory t u}
    (plan : CopyUnitPlan rho) : (plan.familiesAt pre).length≤plan.units := by
  revert pre
  induction plan with
  | nil => intro pre;exact Nat.le_refl _
  | cons blocks rest ih =>
    intro pre
    change (blocks.filterMap (copyUnitFamily pre)++rest.familiesAt _).length≤blocks.length+rest.units
    rw [List.length_append]
    exact Nat.add_le_add (filterMap_length_bound _ _) (ih _)

private theorem distinct_subset_length {A : Type} (xs ys : List A)
    (distinct : xs.Nodup) (included : ∀ x∈xs,x∈ys) : xs.length≤ys.length := by
  classical
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    have pieces := List.nodup_cons.mp distinct
    have hx := included x List.mem_cons_self
    have reduced : ∀ z∈xs,z∈ys.erase x := by
      intro z hz
      apply (List.mem_erase_of_ne ?_).mpr
      · exact included z (List.mem_cons_of_mem _ hz)
      · intro eq
        exact pieces.1 (eq ▸ hz)
    have bound := ih (ys.erase x) pieces.2 reduced
    have size := List.length_erase_of_mem hx
    have positive : 0<ys.length := List.length_pos_of_mem hx
    simp only [List.length_cons]
    omega

/-- Comparison counts genuine nonempty copy units of the competitor, not its
parallel batches, beta edges, administrative work or runtime cost. The complete
needed prefix need not itself terminate. Both histories start at ORIGINAL m. -/
theorem CompleteDerivation.length_le_copy_units
    {m t n : Term} {rho : ParallelHistory m t}
    (complete : CompleteDerivation rho) (needful : CallByNeedHistory rho)
    (sigma : ParallelHistory m n) (normal : BetaNF n)
    (plan : CopyUnitPlan sigma) (valid : plan.Valid (.nil m)) :
    rho.length≤plan.units := by
  have covered : ∀ family∈roundFamilySupport rho,family∈plan.familiesAt (.nil m) := by
    intro family
    refine Quotient.inductionOn family ?_
    intro a member
    have oldUse := (complete.mem_roundFamilySupport a).mp member
    have competitorUse := complete.needed_family_inclusion needful sigma normal a oldUse
    exact plan.familyUsed_mem (.nil m) valid a competitorUse
  have count := distinct_subset_length (roundFamilySupport rho)
    (plan.familiesAt (.nil m)) complete.roundFamilySupport_nodup covered
  rw [complete.roundFamilySupport_length] at count
  exact Nat.le_trans count (plan.familiesAt_length_le (.nil m))

#print axioms Lamping.Lambda.CopyUnitPlan
#print axioms Lamping.Lambda.CopyUnitPlan.Valid
#print axioms Lamping.Lambda.CopyUnitPlan.units
#print axioms Lamping.Lambda.copyUnitFamily
#print axioms Lamping.Lambda.CopyUnitPlan.familiesAt
#print axioms Lamping.Lambda.CopySet.firstSelectedRedex_some
#print axioms Lamping.Lambda.CopySet.copyUnitFamily_member
#print axioms Lamping.Lambda.CopyUnitPlan.familyUsed_mem
#print axioms Lamping.Lambda.CopyUnitPlan.familiesAt_length_le
#print axioms Lamping.Lambda.CompleteDerivation.length_le_copy_units

end Lamping.Lambda
