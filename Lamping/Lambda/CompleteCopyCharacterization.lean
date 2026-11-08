import Lamping.Lambda.CompleteFamiliesExhaustion
import Lamping.Lambda.FamilyCopyAncestor
namespace Lamping.Lambda

/-- AG5.4.8 locally at every actual complete prefix. The nonempty condition
is explicit because a raw maximal CopySet can be empty at a normal form. -/
theorem CompleteDerivation.complete_step_iff_max_copies {ρ : ParallelHistory m t}
    (complete : CompleteDerivation ρ) (step : ParallelStep F t u) :
    CompleteFamilyStep ρ step ↔ F≠[] ∧ MaxCopySet ρ F := by
  constructor
  · intro whole
    obtain ⟨r,member,_⟩ := whole.2
    obtain ⟨_,a,_,_,copy,all⟩ := complete.develops_used.common_copy_ancestor r
    exact ⟨whole.nonempty,whole.maximal_of_common_ancestor r member a copy all⟩
  · rintro ⟨nonempty,maximal⟩
    cases F with
    | nil => exact False.elim (nonempty rfl)
    | cons p ps =>
      let r : RedexOcc t := ⟨p,maximal.1.1 p List.mem_cons_self⟩
      obtain ⟨_,a,_,_,copy,all⟩ := complete.develops_used.common_copy_ancestor r
      exact maximal.complete_of_common_ancestor r List.mem_cons_self a copy all

/-- Histories whose actual steps select nonempty maximal sets of copies.
Selection lists retain the existing membership semantics, including duplicates. -/
inductive MaxCopiesDerivation : ParallelHistory m t → Prop where
  | nil (m) : MaxCopiesDerivation (.nil m)
  | step {ρ : ParallelHistory m t} {F : List Path} {u : Term} {h : ParallelStep F t u} :
      MaxCopiesDerivation ρ → F≠[] → MaxCopySet ρ F →
      MaxCopiesDerivation (ρ.append (.single h))

/-- AG5.4.8 for entire histories, proved by prefixes. No existence of an
extension or termination of family developments is asserted. -/
theorem complete_derivation_iff_max_copies {ρ : ParallelHistory m t} :
    CompleteDerivation ρ ↔ MaxCopiesDerivation ρ := by
  constructor
  · intro complete
    induction complete with
    | nil => exact .nil _
    | step previous whole ih =>
      have result := (previous.complete_step_iff_max_copies _).mp whole
      exact .step ih result.1 result.2
  · intro copies
    induction copies with
    | nil => exact .nil _
    | step previous nonempty maximal ih =>
      exact .step ih ((ih.complete_step_iff_max_copies _).mpr ⟨nonempty,maximal⟩)

end Lamping.Lambda
