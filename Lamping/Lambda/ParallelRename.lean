import Lamping.Lambda.RenameResiduals
import Lamping.Lambda.AtomicProjection
import Lamping.Lambda.DerivationProjection
namespace Lamping.Lambda.Marked

theorem StepAt.rename (h : StepAt p t u) (ρ : Nat → Nat) :
    StepAt p (Marked.rename ρ t) (Marked.rename ρ u) := by
  induction h generalizing ρ with
  | root l b a =>
    simpa only [Marked.rename, rename_contract] using
      (StepAt.root l (Marked.rename (liftRen ρ) b) (Marked.rename ρ a))
  | lam h ih => exact .lam (ih (liftRen ρ))
  | appL h ih => exact .appL (ih ρ)
  | appR h ih => exact .appR (ih ρ)
  | redL h ih => exact .redL (ih (liftRen ρ))
  | redR h ih => exact .redR (ih ρ)

theorem RelativeHistory.rename (h : RelativeHistory ps t u) (ρ : Nat → Nat) :
    RelativeHistory ps (Marked.rename ρ t) (Marked.rename ρ u) := by
  induction h with
  | nil => exact .nil _
  | cons h hs ih => exact .cons (h.rename ρ) ih

end Lamping.Lambda.Marked
namespace Lamping.Lambda

def ParallelStep.rename (h : ParallelStep F t u) (ρ : Nat → Nat) :
    ParallelStep F (Lambda.rename ρ t) (Lambda.rename ρ u) where
  paths := h.paths
  markedTarget := Marked.rename ρ h.markedTarget
  complete := by
    apply (Marked.completeOld_iff F _).mpr
    have completed := (Marked.completeOld_iff F t).mp h.complete
    refine ⟨?_, Marked.normal_rename completed.2 ρ⟩
    simpa only [Marked.mark, Marked.markAt_rename] using completed.1.rename ρ
  target_eq := by rw [Marked.erase_rename, h.target_eq]

@[simp] theorem ParallelStep.rename_paths (h : ParallelStep F t u) (ρ : Nat → Nat) :
    (h.rename ρ).paths = h.paths := rfl

@[simp] theorem ParallelStep.rename_residualSet (h : ParallelStep F t u) (ρ : Nat → Nat) (G : List Path) :
    (h.rename ρ).residualSet G = h.residualSet G := by
  simp only [residualSet, ParallelStep.rename, Marked.setResidualPositions, Marked.trace_rename]

theorem singleContraction_rename (S : BetaAt t p u) (ρ : Nat → Nat) :
    (singleContraction S).rename ρ = singleContraction (S.rename ρ) := by
  apply ParallelStep.ext_data ((singleContraction S).rename ρ) (singleContraction (S.rename ρ)) rfl
  have left := (Marked.completeOld_iff [p] (Lambda.rename ρ t)).mp ((singleContraction S).rename ρ).complete
  have right := (Marked.completeOld_iff [p] (Lambda.rename ρ t)).mp (singleContraction (S.rename ρ)).complete
  exact Marked.complete_unique ⟨left.1.steps,left.2⟩ ⟨right.1.steps,right.2⟩

def ParallelHistory.rename (ρ : Nat → Nat) : ParallelHistory t u →
    ParallelHistory (Lambda.rename ρ t) (Lambda.rename ρ u)
  | .nil _ => .nil _
  | .cons h tail => .cons (h.rename ρ) (tail.rename ρ)

@[simp] theorem ParallelHistory.rename_derivation_paths (σ : ParallelHistory t u) (ρ : Nat → Nat) :
    (σ.rename ρ).derivation.paths = σ.derivation.paths := by
  induction σ with
  | nil => rfl
  | cons h tail ih =>
    change h.paths ++ (tail.rename ρ).derivation.paths = h.paths ++ tail.derivation.paths
    rw [ih]

theorem Atomic.rename {σ : ParallelHistory t u} (ha : Atomic σ) (ρ : Nat → Nat) : Atomic (σ.rename ρ) := by
  induction ha with
  | nil => exact .nil _
  | cons S hs ih =>
    simp only [ParallelHistory.rename, singleContraction_rename]
    exact .cons (S.rename ρ) ih

@[simp] theorem ParallelHistory.rename_append (σ : ParallelHistory t u) (τ : ParallelHistory u v) (ρ : Nat → Nat) :
    (σ.append τ).rename ρ = (σ.rename ρ).append (τ.rename ρ) := by
  induction σ with
  | nil => rfl
  | cons h tail ih => exact congrArg (ParallelHistory.cons (h.rename ρ)) (ih τ)

@[simp] theorem ParallelHistory.rename_length (σ : ParallelHistory t u) (ρ : Nat → Nat) :
    (σ.rename ρ).length = σ.length := by
  induction σ with
  | nil => rfl
  | cons h tail ih => simp only [rename, length, ih]

private theorem cons_selection_cast {F G : List Path} (eq : F = G)
    (h : ParallelStep F t u) (tail : ParallelHistory u v) :
    ParallelHistory.cons (eq ▸ h) tail = ParallelHistory.cons h tail := by
  cases eq
  rfl

private theorem projection_first_cast {F G : List Path} (eq : F = G)
    {h : ParallelStep F t u} (row : StepProjection h σ τ last) :
    StepProjection (eq ▸ h) σ τ last := by
  cases eq
  exact row

theorem StepProjection.rename (row : StepProjection step σ τ last) (ρ : Nat → Nat) :
    StepProjection (step.rename ρ) (σ.rename ρ) (τ.rename ρ) (last.rename ρ) := by
  induction row with
  | nil step => exact .nil (step.rename ρ)
  | @cons F G t u v w x σ y τ H last sq tail ih =>
    have left := sq.first.rename_residualSet ρ G
    have right := sq.second.rename_residualSet ρ F
    let renamed : ParallelMovesSquare _ _ _ _ _ _ :=
      ⟨sq.first.rename ρ, sq.second.rename ρ,
        left.symm ▸ sq.afterFirst.rename ρ, right.symm ▸ sq.afterSecond.rename ρ⟩
    have ih' : StepProjection renamed.afterSecond (σ.rename ρ) (τ.rename ρ) (last.rename ρ) := by
      exact projection_first_cast right.symm ih
    have built := StepProjection.cons renamed ih'
    simpa only [renamed, ParallelHistory.rename, cons_selection_cast] using built

end Lamping.Lambda
