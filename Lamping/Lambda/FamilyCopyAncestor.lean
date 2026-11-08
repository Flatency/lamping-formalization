import Lamping.Lambda.CanonicalFamilyEvents
import Lamping.Lambda.CopySetRepresentation
namespace Lamping.Lambda

/-- At the endpoint of an actual development of its own used families,
each whole current family has one canonical common Copy ancestor. The
development is given; no completion or termination theorem is invoked. -/
theorem DevelopsFamilies.common_copy_ancestor {ρ : ParallelHistory m t}
    (development : DevelopsFamilies ρ (FamilyUsed ρ)) (r : RedexOcc t) :
    ∃ (run : ExtractionRun m) (ancestor : RedexWithHistory m),
      CanonicalRun run ∧ RunRepresents run ancestor ∧
      Copy ancestor ⟨t,ρ,r⟩ ∧
      ∀ s : RedexOcc t, FamilyEq ⟨t,ρ,r⟩ ⟨t,ρ,s⟩ → Copy ancestor ⟨t,ρ,s⟩ := by
  obtain ⟨run,ancestor,canonical,represented,family⟩ :=
    (show RedexWithHistory m from ⟨t,ρ,r⟩).canonical_exists
  have whole (s : RedexOcc t) (same : FamilyEq ⟨t,ρ,r⟩ ⟨t,ρ,s⟩) :
      Copy ancestor ⟨t,ρ,s⟩ := by
    have related := family.symm.trans same
    exact canonical_copy_of_development canonical represented related
      (canonical_prefix_relative canonical represented related) development
  exact ⟨run,ancestor,canonical,represented,whole r (.refl _),whole⟩

/-- The entire current family, rather than only a fixed ancestor's
arbitrary subset, is represented by one actual extension. -/
theorem DevelopsFamilies.family_copySet {ρ : ParallelHistory m t}
    (development : DevelopsFamilies ρ (FamilyUsed ρ)) (r : RedexOcc t) :
    ∃ F : List Path, CopySet ρ F ∧ r.val∈F ∧
      ∀ s : RedexOcc t,s.val∈F ↔ FamilyEq ⟨t,ρ,r⟩ ⟨t,ρ,s⟩ := by
  obtain ⟨_,ancestor,_,_,copy,whole⟩ := development.common_copy_ancestor r
  exact copy.family_copySet ancestor r whole

end Lamping.Lambda
