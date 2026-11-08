import Lamping.Lambda.FamilyStandardization
import Lamping.Lambda.InitialFamilies
import Lamping.Lambda.StandardizationExistence
namespace Lamping.Checks.FamilyStandardization
open Lambda
abbrev delta : Term := .lam (.app (.var 0) (.var 0))
abbrev omegaTerm : Term := .app delta delta
abbrev identity : Term := .lam (.var 0)
abbrev source : Term := .app (.lam identity) omegaTerm
def argument : BetaAt source [.arg] source := ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
def eraseArgument : BetaAt source [] identity := ⟨identity,omegaTerm,rfl,rfl⟩
def longHistory : ParallelHistory source identity :=
  .cons (singleContraction argument) (.single (singleContraction eraseArgument))
def shortHistory : ParallelHistory source identity := .single (singleContraction eraseArgument)
def erasedFamily : RedexWithHistory source := ⟨source,.nil _,⟨[.arg],argument.redex⟩⟩

theorem actual_permutation : PermEq longHistory shortHistory := by
  have first : (singleContraction argument).residualSet [[]]=[[]] := by decide
  have second : (singleContraction eraseArgument).residualSet [[.arg]]=[] := by decide
  let square : ParallelMovesSquare [[.arg]] [[]] source source identity identity :=
    ⟨singleContraction argument,singleContraction eraseArgument,
      first.symm ▸ singleContraction eraseArgument,second.symm ▸ ParallelStep.empty identity⟩
  have generated := PermEq.moves square
  have delete := PermEq.prepend shortHistory (PermEq.empty (ParallelStep.empty identity))
  rw [ParallelHistory.append_nil] at delete
  exact generated.trans (by simpa [square,ParallelHistory.cons_selection_cast] using delete)

theorem erased_event : FamilyUsed longHistory erasedFamily := .head (by simp) (.refl _)

theorem no_erased_event : ¬FamilyUsed shortHistory erasedFamily := by
  intro used
  cases used with
  | @head _ _ _ _ _ _ _ _ r selected family =>
    have root : r.val=[] := List.mem_singleton.mp selected
    have equal := (initial_families_injective r ⟨[.arg],argument.redex⟩).mp family
    have paths := congrArg Subtype.val equal
    rw [root] at paths
    cases paths
  | tail impossible => cases impossible

/-- Generated permutation may delete a redundant family event: FAM is not
an invariant of arbitrary PermEq. Both schedules and the omitted event are real. -/
example : PermEq longHistory shortHistory ∧ FamilyUsed longHistory erasedFamily ∧
    ¬FamilyUsed shortHistory erasedFamily := ⟨actual_permutation,erased_event,no_erased_event⟩

example : ¬(∀ (a : RedexWithHistory source), FamilyUsed longHistory a → FamilyUsed shortHistory a) := by
  intro invariant
  exact no_erased_event (invariant erasedFamily erased_event)

example (ρ : ParallelHistory t u) : ∃ σ : ParallelHistory t u,
    Atomic σ ∧ Standard σ ∧ PermEq ρ σ ∧ RelativeFamilies σ (FamilyUsed ρ) :=
  atomic_standardization_exists_relative ρ

example : ∃ σ : ParallelHistory source identity,
    Atomic σ ∧ Standard σ ∧ PermEq longHistory σ ∧ RelativeFamilies σ (FamilyUsed longHistory) :=
  atomic_standardization_exists_relative longHistory

def invalid : ParallelStep [[.fn],[.fn]] (.var 0) (.var 0) :=
  ⟨[],.var 0,⟨.nil _,rfl⟩,rfl⟩
example : ∃ σ : ParallelHistory (.var 0) (.var 0), Atomic σ ∧ Standard σ ∧
    PermEq (.single invalid) σ ∧ RelativeFamilies σ (FamilyUsed (.single invalid)) :=
  atomic_standardization_exists_relative (.single invalid)

#print axioms StepProjection.used_bottom
#print axioms FamilyUsedAt.pull_factor_support
#print axioms RightHistory.pull_selected_supported
#print axioms ParallelHistory.extract_minimal_supported
#print axioms atomic_standardization_exists_supported
#print axioms atomic_standardization_exists_relative
#print axioms actual_permutation
#print axioms no_erased_event
end Lamping.Checks.FamilyStandardization
