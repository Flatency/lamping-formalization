import Lamping.Lambda.PermutationResidual
namespace Lamping.Lambda

/-- A nonempty *whole current family*, relative to the given history. Validity
 disallows junk paths in the finite selection; maximality is only at this term. -/
def CompleteFamilyStep (ρ : ParallelHistory m t) (_h : ParallelStep F t u) : Prop :=
  (∀ p ∈ F, ∃ z, subtermAt t p = some z ∧ IsRedex z) ∧
  ∃ r : RedexOcc t, r.val ∈ F ∧ ∀ s : RedexOcc t,
    s.val ∈ F ↔ FamilyEq ⟨t, ρ, r⟩ ⟨t, ρ, s⟩

/-- AG5.4.6 is a condition on every finite prefix. It contains no assertion
 that the last term has no redex, and no general completion operation. -/
inductive CompleteDerivation : ParallelHistory m t → Prop where
  | nil (m) : CompleteDerivation (.nil m)
  | step : CompleteDerivation ρ → CompleteFamilyStep ρ h →
      CompleteDerivation (ρ.append (.single h))

 theorem CompleteFamilyStep.nonempty {ρ : ParallelHistory m t} {step : ParallelStep F t u} (h : CompleteFamilyStep ρ step) : F ≠ [] := by
   obtain ⟨_, r, hr, _⟩ := h
   intro he; rw [he] at hr; exact List.not_mem_nil hr

 theorem CompleteFamilyStep.same_family {ρ : ParallelHistory m t} {step : ParallelStep F t u} (h : CompleteFamilyStep ρ step)
     (r s : RedexOcc t) (hr : r.val ∈ F) (hs : s.val ∈ F) :
     FamilyEq ⟨t, ρ, r⟩ ⟨t, ρ, s⟩ := by
   obtain ⟨_, q, _, hq⟩ := h
   exact .trans (.symm ((hq r).mp hr)) ((hq s).mp hs)

 theorem CompleteFamilyStep.maximal {ρ : ParallelHistory m t} {step : ParallelStep F t u} (h : CompleteFamilyStep ρ step)
     (r s : RedexOcc t) (hr : r.val ∈ F)
     (he : FamilyEq ⟨t, ρ, r⟩ ⟨t, ρ, s⟩) : s.val ∈ F := by
   obtain ⟨_, q, _, hq⟩ := h
   exact (hq s).mpr (.trans ((hq r).mp hr) he)
end Lamping.Lambda

