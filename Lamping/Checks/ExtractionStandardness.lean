import Lamping.Lambda.ExtractionStandardness
import Lamping.Lambda.StandardizationGeneral
namespace Lamping.Checks.ExtractionStandardness
open Lambda
abbrev delta : Term := .lam (.app (.var 0) (.var 0))
abbrev omegaTerm : Term := .app delta delta
abbrev twins : Term := .app omegaTerm omegaTerm
def rightStep : BetaAt twins [.arg] twins := ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
def leftStep : BetaAt twins [.fn] twins := ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
def rightThenLeft : ParallelHistory twins twins := .cons (singleContraction rightStep) (.single (singleContraction leftStep))
theorem rightThenLeft_not_standard : ¬Standard rightThenLeft := by
  intro standard
  cases standard with
  | cons _ witness lo noReturn rest =>
    have atRight : witness.val=[.arg] := List.mem_singleton.mp lo.1
    let earlier : RedexOcc twins := ⟨[.fn],leftStep.redex⟩
    apply noReturn earlier (by rw [atRight]; exact .branch [] [])
      (.single (singleContraction rightStep)) (singleContraction leftStep) (.nil _) rfl earlier (leftmost_singleton earlier)
    change (singleContraction rightStep).derivation.Residual earlier earlier
    exact (rightStep.disjoint_residual_iff earlier (DisjointPositions.head_ne (by intro eq; cases eq)) earlier).mpr rfl
/-- Pointed source-prefix standardness does not assert full-run standardness. -/
example : PrefixStandard (.of rightThenLeft (.cons rightStep (.single leftStep))) ∧ ¬Standard rightThenLeft := by
  refine ⟨?_,rightThenLeft_not_standard⟩
  apply (prefixStandard_append_last_iff (.single (singleContraction rightStep)) (.single rightStep) leftStep).mpr
  exact Standard.single_step _ ⟨[.arg],rightStep.redex⟩ (leftmost_singleton _)
/-- Actual generated permutation does not make Standard itself invariant. -/
example : ∃ σ : ParallelHistory twins twins, Standard σ ∧ PermEq rightThenLeft σ ∧ ¬Standard rightThenLeft := by
  obtain ⟨σ,standard,perm⟩ := standardization_exists rightThenLeft
  exact ⟨σ,standard,perm,rightThenLeft_not_standard⟩
example : PrefixStandard (.of (.single (singleContraction leftStep)) (.single leftStep)) :=
  residual_prefix_standard (.nil _) (.nil _) rightStep leftStep leftStep (by
    apply (prefixStandard_append_last_iff (.single (singleContraction rightStep)) (.single rightStep) leftStep).mpr
    exact Standard.single_step _ ⟨[.arg],rightStep.redex⟩ (leftmost_singleton _))
example (ρ σ : ParallelHistory t u) (atomic : Atomic ρ) (r : RedexOcc t)
    (noReturn : DoesNotReturnLeft r ρ) (perm : PermEq ρ σ) : DoesNotReturnLeft r σ :=
  noReturn.permutation atomic perm
#print axioms DoesNotReturnLeft.permutation
#print axioms Standard.replace_suffix_extension
#print axioms UsedSource.internal
#print axioms UsedSource.project_unique
#print axioms BetaAt.region_left_image
#print axioms Atomic.region_standard_reflect
#print axioms prefixStandard_append_last_iff
#print axioms residual_prefix_standard
#print axioms region_prefix_standard
example (step : ExtractionStep r s) (standard : PrefixStandard r) : PrefixStandard s :=
  step.prefix_standard standard
example (steps : Extraction r s) (standard : PrefixStandard r) : PrefixStandard s :=
  steps.prefix_standard standard
example (standard : PrefixStandard r) : ∃ s, Extraction r s ∧ CanonicalRun s :=
  canonical_extraction_exists standard
def duplicateRoot : BetaAt (.app (.lam (.app (.var 0) (.var 0))) omegaTerm) [] twins :=
  ⟨.app (.var 0) (.var 0),omegaTerm,rfl,rfl⟩
def copyTwice : ParallelHistory twins twins := .cons (singleContraction leftStep) (.single (singleContraction leftStep))
theorem copyTwice_atomic : Atomic copyTwice := .cons leftStep (.single leftStep)
/-- Nonlinear argument extraction with two real chosen-copy contractions,
requiring Standard only of the actual prefix R;left before its last left. -/
example : ∃ (w : Term) (original : ParallelHistory (.app (.lam (.app (.var 0) (.var 0))) omegaTerm) w)
    (ordinary : Atomic original), PrefixStandard (.of original ordinary) := by
  have inside : Internal [.fn] copyTwice := by
    intro q hq
    change q∈[[.fn],[.fn]] at hq
    have same : q=[.fn] := by simpa using hq
    exact ⟨[],by simpa using same⟩
  obtain ⟨w,original,ordinary,lift,_⟩ := argument_lift_exists duplicateRoot rfl (occurrence:=[.fn]) rfl copyTwice inside
  have prefixStandard : Standard ((ParallelHistory.single (singleContraction duplicateRoot)).append (.single (singleContraction leftStep))) := by
    apply Standard.cons (singleContraction duplicateRoot) ⟨[],duplicateRoot.redex⟩ (leftmost_singleton _)
    · intro old before
      change LeftOf old.val [] at before
      have impossible : ∀ p : Path, ¬LeftOf p [] := by intro p h; cases h
      exfalso
      exact impossible old.val before
    · exact Standard.single_step _ ⟨[.fn],leftStep.redex⟩ (leftmost_singleton _)
  have sourceStandard : PrefixStandard (.of ((ParallelHistory.single (singleContraction duplicateRoot)).append copyTwice)
      ((Atomic.single duplicateRoot).append copyTwice_atomic)) := by
    exact (prefixStandard_append_last_iff _ ((Atomic.single duplicateRoot).append (.single leftStep)) leftStep).mpr prefixStandard
  exact ⟨w,original,ordinary,lift.prefix_standard copyTwice_atomic ordinary (by decide) (.nil _) (.nil _) sourceStandard⟩
#print axioms UsedSource.region_rename
#print axioms Atomic.region_rename_standard_reflect
#print axioms UsedSource.common_prefix
#print axioms Standard.replace_suffix_used
#print axioms argument_used_inclusion
#print axioms ArgumentLift.prefix_standard
#print axioms ExtractionStep.prefix_standard
#print axioms Extraction.prefix_standard
#print axioms canonical_extraction_exists
end Lamping.Checks.ExtractionStandardness
