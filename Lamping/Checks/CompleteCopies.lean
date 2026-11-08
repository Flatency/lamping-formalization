import Lamping.Lambda.CompleteCopyCharacterization
import Lamping.Lambda.InitialCompleteCopies
import Lamping.Lambda.SingleContraction
namespace Lamping.Checks.CompleteCopies
open Lambda
private def delta : Term := .lam (.app (.var 0) (.var 0))
private def omegaTerm : Term := .app delta delta
private def beta : BetaAt omegaTerm [] omegaTerm := ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
private def redex : RedexOcc omegaTerm := ⟨[],beta.redex⟩
private def one : ParallelHistory omegaTerm omegaTerm := .single (singleContraction beta)
private def two : ParallelHistory omegaTerm omegaTerm := one.append one
private theorem only_redex (s : RedexOcc omegaTerm) : s=redex := by
  have positions : redexPositions omegaTerm=[[]] := by decide
  have member := (mem_redexPositions omegaTerm s.val).mpr s.property
  rw [positions] at member
  exact Subtype.ext (List.mem_singleton.mp member)
private theorem whole (ρ : ParallelHistory omegaTerm omegaTerm) :
    CompleteFamilyStep ρ (singleContraction beta) := by
  refine ⟨?_,redex,(by simp [redex]),?_⟩
  · intro p member
    cases List.mem_singleton.mp member
    exact beta.redex
  · intro s
    rw [only_redex s]
    exact ⟨fun _ => .refl _,fun _ => List.mem_singleton_self _⟩
private theorem first_complete : CompleteDerivation one :=
  .step (.nil _) (whole (.nil _))
private theorem second_complete : CompleteDerivation two :=
  .step first_complete (whole one)
-- The program can return to precisely the same closed term and redex path,
-- yet the successive root contractions belong to distinct families.
example : Closed omegaTerm := by simp [Closed,Scoped,omegaTerm,delta]
example : ¬FamilyEq ⟨omegaTerm,.nil omegaTerm,redex⟩ ⟨omegaTerm,two,redex⟩ := by
  intro family
  apply first_complete.no_future_family one redex
  exact FamilyUsedAt.head (by simp [redex]) family
example : DevelopsFamilies two (FamilyUsed two) := second_complete.develops_used
example : MaxCopySet one [[]] :=
  ((first_complete.complete_step_iff_max_copies (singleContraction beta)).mp (whole one)).2
example : MaxCopiesDerivation two := complete_derivation_iff_max_copies.mp second_complete
example : CompleteDerivation two :=
  complete_derivation_iff_max_copies.mpr (complete_derivation_iff_max_copies.mp second_complete)
-- Repetition changes neither selected membership nor the complete-family theorem.
private def repeated := (singleContraction beta).reindex [[],[]] (fun p => by simp)
example : MaxCopySet one [[],[]] := by
  have valid : CompleteFamilyStep one repeated := by
    refine ⟨?_,redex,(by simp [redex]),?_⟩
    · intro p member
      have eq : p=[] := by simpa using member
      cases eq
      exact beta.redex
    · intro s
      rw [only_redex s]
      exact ⟨fun _ => .refl _,fun _ => by simp [redex]⟩
  exact ((first_complete.complete_step_iff_max_copies repeated).mp valid).2
#print axioms CompleteDerivation.no_future_family
#print axioms CompleteDerivation.develops_used
#print axioms CompleteDerivation.complete_step_iff_max_copies
#print axioms complete_derivation_iff_max_copies
end Lamping.Checks.CompleteCopies
