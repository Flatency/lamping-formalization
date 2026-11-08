import Lamping.Lambda.CanonicalExistence
namespace Lamping.Checks.CanonicalExistence
open Lambda
example (a : RedexWithHistory m) :
    ∃ (r : ExtractionRun m) (b : RedexWithHistory m), CanonicalRun r ∧ RunRepresents r b ∧ FamilyEq a b :=
  a.canonical_exists
abbrev delta : Term := .lam (.app (.var 0) (.var 0))
abbrev omegaTerm : Term := .app delta delta
def pointedEmpty : RedexWithHistory omegaTerm :=
  ⟨omegaTerm,.single (ParallelStep.empty omegaTerm),⟨[],⟨omegaTerm,rfl,True.intro⟩⟩⟩
/-- A real non-Atomic parallel history is permitted as input; its original
history is not silently reinterpreted as an extraction run. -/
example : ¬Atomic pointedEmpty.history := by
  intro atomic
  have lengths := atomic.paths_length
  change 0=1 at lengths
  omega
example : ∃ (r : ExtractionRun omegaTerm) (b : RedexWithHistory omegaTerm),
    CanonicalRun r ∧ RunRepresents r b ∧ FamilyEq pointedEmpty b := pointedEmpty.canonical_exists
#print axioms RedexWithHistory.canonical_exists
end Lamping.Checks.CanonicalExistence
