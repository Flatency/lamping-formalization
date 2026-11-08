import Lamping.Lambda.FamilyProjectionEvents
import Lamping.Lambda.StandardizationExistence
namespace Lamping.Lambda

/-- If no current redex belongs to X, an actual history whose events all
belong to X has no contractions modulo generated permutation. Invalid and
empty selected lists are eliminated by actual complete-step proofs. -/
theorem FamilyUsedAt.empty_of_absent {X : RedexWithHistory m → Prop} {ρ : ParallelHistory t u} (pre : ParallelHistory m t)
    (relative : ∀ a, FamilyUsedAt pre ρ a → X a)
    (absent : ∀ r : RedexOcc t, ¬X ⟨t,pre,r⟩) :
    ∃ eq : u=t, PermEq (eq ▸ ρ) (.nil t) := by
  induction ρ with
  | nil => exact ⟨rfl,.refl _⟩
  | @cons t v u F h tail ih =>
    have none : ∀ r : RedexOcc t, r.val∉F := by
      intro r selected
      exact absent r (relative _ (.head selected (.refl _)))
    have endpoint := h.no_actual_endpoint none
    subst v
    have empty := PermEq.no_actual_selection h none
    have perm : PermEq (pre.append (.single h)) pre := by
      simpa only [ParallelHistory.append_nil] using PermEq.prepend pre empty
    have tailRelative : ∀ a, FamilyUsedAt pre tail a → X a := by
      intro a used
      exact relative a (.tail (used.prefix_permutation perm.symm))
    obtain ⟨eq,rest⟩ := ih pre tailRelative absent
    cases eq
    refine ⟨rfl,?_⟩
    exact PermEq.comp empty rest

/-- The finite join argument of AG5.4.3(ii): any given relative history is
covered by any given exhausted development. No finite-development existence,
termination, degree/label invariant, or Ex5.4.9 is used. -/
theorem RelativeFamilies.prefix_development {σ : ParallelHistory m t} {ρ : ParallelHistory m u}
    (relative : RelativeFamilies σ X) (development : DevelopsFamilies ρ X) : HistoryPrefix σ ρ := by
  obtain ⟨w,σ',ρ',grid⟩ := HistoryProjection.exists_projection σ ρ
  have projectedRelative : ∀ a, FamilyUsedAt ρ σ' a → X a := by
    intro a used
    exact relative a (grid.used_left (.nil m) used)
  obtain ⟨eq,empty⟩ := FamilyUsedAt.empty_of_absent ρ projectedRelative development.2
  cases eq
  refine ⟨ρ',?_⟩
  have right := PermEq.prepend ρ empty
  rw [ParallelHistory.append_nil] at right
  exact grid.permutation.trans right

end Lamping.Lambda
