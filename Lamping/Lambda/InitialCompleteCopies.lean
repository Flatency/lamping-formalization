import Lamping.Lambda.CopySetRepresentation
import Lamping.Lambda.InitialFamilies
namespace Lamping.Lambda

private theorem initial_ancestor (r s : RedexOcc m)
    (family : FamilyEq ⟨m,.nil m,r⟩ ⟨m,.nil m,s⟩) :
    Copy ⟨m,.nil m,r⟩ ⟨m,.nil m,s⟩ := by
  have equal := (initial_families_injective r s).mp family
  cases equal
  exact Copy.refl _

/-- The genuine empty-prefix base case of the complete/maximal-copies
characterization. General complete prefixes still require a separate
canonical Copy-ancestor theorem. -/
theorem initial_complete_iff_max_copies (step : ParallelStep F m t) :
    CompleteFamilyStep (.nil m) step ↔ F≠[] ∧ MaxCopySet (.nil m) F := by
  constructor
  · intro complete
    obtain ⟨r,member,_⟩ := complete.2
    exact ⟨complete.nonempty,complete.maximal_of_common_ancestor r member
      ⟨m,.nil m,r⟩ (Copy.refl _) (fun s family => initial_ancestor r s family)⟩
  · rintro ⟨nonempty,maximal⟩
    cases F with
    | nil => exact False.elim (nonempty rfl)
    | cons p ps =>
      let r : RedexOcc m := ⟨p,maximal.1.1 p List.mem_cons_self⟩
      exact maximal.complete_of_common_ancestor r List.mem_cons_self ⟨m,.nil m,r⟩
        (Copy.refl _) (fun s family => initial_ancestor r s family)

end Lamping.Lambda
