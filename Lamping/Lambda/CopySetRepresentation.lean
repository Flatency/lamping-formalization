import Lamping.Lambda.MaximalCopies
import Lamping.Lambda.HistoryCancellation
namespace Lamping.Lambda

/-- Different actual extensions from one ancestor to the same current
history have exactly the same old residuals. This uses general prefix
cancellation, rather than endpoint equality. -/
theorem Copy.extension_residual_iff (a : RedexWithHistory m) (ρ : ParallelHistory m t)
    (τ υ : ParallelHistory a.target t)
    (left : PermEq (a.history.append τ) ρ) (right : PermEq (a.history.append υ) ρ)
    (s : RedexOcc t) : τ.derivation.Residual a.redex s ↔ υ.derivation.Residual a.redex s :=
  ((left.trans right.symm).cancel_prefix a.history).residual a.redex s

/-- A genuine common Copy ancestor of a whole current family yields one
fixed actual extension representing that family. No complete-prefix or
canonical-ancestor theorem is assumed to have been proved by this lemma. -/
theorem Copy.family_copySet {ρ : ParallelHistory m t} (a : RedexWithHistory m)
    (r : RedexOcc t) (initial : Copy a ⟨t,ρ,r⟩)
    (whole : ∀ s : RedexOcc t,FamilyEq ⟨t,ρ,r⟩ ⟨t,ρ,s⟩ → Copy a ⟨t,ρ,s⟩) :
    ∃ F : List Path, CopySet ρ F ∧ r.val∈F ∧
      ∀ s : RedexOcc t,s.val∈F ↔ FamilyEq ⟨t,ρ,r⟩ ⟨t,ρ,s⟩ := by
  classical
  obtain ⟨τ,perm,residual⟩ := initial
  let F := (redexPositions t).filter (fun p => decide
    (∃ s : RedexOcc t,s.val=p ∧ τ.derivation.Residual a.redex s))
  have members (s : RedexOcc t) : s.val∈F ↔ τ.derivation.Residual a.redex s := by
    simp only [F,List.mem_filter,decide_eq_true_eq]
    constructor
    · rintro ⟨_,q,same,hq⟩
      have equal : q=s := Subtype.ext same
      exact equal ▸ hq
    · intro h
      exact ⟨(mem_redexPositions t s.val).mpr s.property,s,rfl,h⟩
  have valid : SelectionValid t F := by
    intro p hp
    exact (mem_redexPositions t p).mp (List.mem_filter.mp hp).1
  refine ⟨F,⟨valid,a,τ,perm,members⟩,(members r).mpr residual,?_⟩
  intro s
  rw [members s]
  constructor
  · intro hs
    exact .trans (.symm (.copy ⟨τ,perm,residual⟩)) (.copy ⟨τ,perm,hs⟩)
  · intro family
    obtain ⟨υ,other,old⟩ := whole s family
    exact (Copy.extension_residual_iff a ρ τ υ perm other s).mpr old

theorem CopySet.selection_congr {ρ : ParallelHistory m t} (copySet : CopySet ρ F)
    (same : ∀ p,p∈F ↔ p∈G) : CopySet ρ G := by
  obtain ⟨valid,a,extension,perm,members⟩ := copySet
  refine ⟨(fun p hp => valid p ((same p).mpr hp)),a,extension,perm,?_⟩
  intro s
  exact (same s.val).symm.trans (members s)

/-- The complete-to-maximal wrapper once the substantive common-ancestor
bridge has supplied actual Copy legs for this whole current family. -/
theorem CompleteFamilyStep.maximal_of_common_ancestor
    {ρ : ParallelHistory m t} {step : ParallelStep F t u}
    (complete : CompleteFamilyStep ρ step) (r : RedexOcc t) (member : r.val∈F)
    (a : RedexWithHistory m) (copy : Copy a ⟨t,ρ,r⟩)
    (whole : ∀ s : RedexOcc t,FamilyEq ⟨t,ρ,r⟩ ⟨t,ρ,s⟩ → Copy a ⟨t,ρ,s⟩) :
    MaxCopySet ρ F := by
  obtain ⟨G,copySet,_,family⟩ := copy.family_copySet a r whole
  have congruence : ∀ p,p∈G ↔ p∈F := by
    intro p
    constructor
    · intro hp
      let s : RedexOcc t := ⟨p,copySet.1 p hp⟩
      exact complete.maximal r s member ((family s).mp hp)
    · intro hp
      let s : RedexOcc t := ⟨p,complete.1 p hp⟩
      exact (family s).mpr (complete.same_family r s member hp)
  exact complete.maximal_copySet (copySet.selection_congr congruence)

/-- The maximal-to-complete wrapper retains the necessary nonempty-step
condition. Common ancestors are real Copy witnesses, not bare endpoints. -/
theorem MaxCopySet.complete_of_common_ancestor
    {ρ : ParallelHistory m t} {step : ParallelStep F t u}
    (maximal : MaxCopySet ρ F) (r : RedexOcc t) (member : r.val∈F)
    (a : RedexWithHistory m) (copy : Copy a ⟨t,ρ,r⟩)
    (whole : ∀ s : RedexOcc t,FamilyEq ⟨t,ρ,r⟩ ⟨t,ρ,s⟩ → Copy a ⟨t,ρ,s⟩) :
    CompleteFamilyStep ρ step := by
  obtain ⟨G,copySet,_,family⟩ := copy.family_copySet a r whole
  have subset : SelectionSubset F G := by
    intro p hp
    let s : RedexOcc t := ⟨p,maximal.1.1 p hp⟩
    exact (family s).mpr (maximal.1.same_family r s member hp)
  have reverse := maximal.2 G copySet subset
  refine ⟨maximal.1.1,r,member,?_⟩
  intro s
  exact ⟨fun hs => (family s).mp (subset s.val hs),
    fun hs => reverse s.val ((family s).mpr hs)⟩

end Lamping.Lambda
