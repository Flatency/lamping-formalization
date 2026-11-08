import Lamping.Lambda.FamilyCopyAncestor
import Lamping.Lambda.CompleteFamiliesExhaustion
namespace Lamping.Lambda

/-- Every whole current family after a complete prefix has a canonical
common Copy ancestor. Complete prefixes need not end in normal form. -/
theorem CompleteDerivation.common_copy_ancestor {ρ : ParallelHistory m t}
    (complete : CompleteDerivation ρ) (r : RedexOcc t) :
    ∃ (run : ExtractionRun m) (ancestor : RedexWithHistory m),
      CanonicalRun run ∧ RunRepresents run ancestor ∧
      Copy ancestor ⟨t,ρ,r⟩ ∧
      ∀ s : RedexOcc t, FamilyEq ⟨t,ρ,r⟩ ⟨t,ρ,s⟩ → Copy ancestor ⟨t,ρ,s⟩ :=
  complete.develops_used.common_copy_ancestor r

theorem CompleteDerivation.family_copySet {ρ : ParallelHistory m t}
    (complete : CompleteDerivation ρ) (r : RedexOcc t) :
    ∃ F : List Path, CopySet ρ F ∧ r.val∈F ∧
      ∀ s : RedexOcc t,s.val∈F ↔ FamilyEq ⟨t,ρ,r⟩ ⟨t,ρ,s⟩ :=
  complete.develops_used.family_copySet r

/-- One actual extension represents exactly the entire current family.
Different Copy witnesses have been unified by history cancellation. -/
theorem CompleteDerivation.family_residual_representation {ρ : ParallelHistory m t}
    (complete : CompleteDerivation ρ) (r : RedexOcc t) :
    ∃ (ancestor : RedexWithHistory m) (extension : ParallelHistory ancestor.target t),
      PermEq (ancestor.history.append extension) ρ ∧
      ∀ s : RedexOcc t, FamilyEq ⟨t,ρ,r⟩ ⟨t,ρ,s⟩ ↔
        extension.derivation.Residual ancestor.redex s := by
  obtain ⟨_,ancestor,_,_,copy,whole⟩ := complete.common_copy_ancestor r
  obtain ⟨extension,perm,old⟩ := copy
  refine ⟨ancestor,extension,perm,?_⟩
  intro s
  constructor
  · intro family
    obtain ⟨other,otherPerm,residual⟩ := whole s family
    exact (Copy.extension_residual_iff ancestor ρ extension other perm otherPerm s).mpr residual
  · intro residual
    exact .trans (.symm (.copy ⟨extension,perm,old⟩)) (.copy ⟨extension,perm,residual⟩)

end Lamping.Lambda
