import Lamping.Lambda.ParallelRename
import Lamping.Lambda.ExtractionClosure
import Lamping.Lambda.ExtractionConfluence
namespace Lamping.Lambda

theorem occurrenceRenaming_lift (ρ : Nat → Nat) (p : Path) :
    occurrenceRenaming (liftRen ρ) p = liftRen (occurrenceRenaming ρ p) := by
  induction p generalizing ρ with
  | nil => rfl
  | cons s p ih => cases s <;> simp only [occurrenceRenaming, ih]

theorem occurrenceRenaming_binder_iff (ρ : Nat → Nat) (p : Path) (i : Nat) :
    occurrenceRenaming (liftRen ρ) p i = binderDepth p ↔ i = binderDepth p := by
  induction p generalizing ρ i with
  | nil => cases i <;> simp [occurrenceRenaming, binderDepth, liftRen]
  | cons s p ih =>
    cases s with
    | fn => exact ih ρ i
    | arg => exact ih ρ i
    | body =>
      change occurrenceRenaming (liftRen (liftRen ρ)) p i = binderDepth p + 1 ↔ i = binderDepth p + 1
      rw [occurrenceRenaming_lift]
      cases i with
      | zero => simp only [liftRen, Nat.zero_ne_add_one]
      | succ i =>
        change (occurrenceRenaming (liftRen ρ) p i).succ = (binderDepth p).succ ↔ i.succ = (binderDepth p).succ
        constructor
        · intro h; exact congrArg Nat.succ ((ih ρ i).mp (Nat.succ.inj h))
        · intro h; exact congrArg Nat.succ ((ih ρ i).mpr (Nat.succ.inj h))

theorem ArgumentOccurrence.rename (ho : ArgumentOccurrence b p) (ρ : Nat → Nat) :
    ArgumentOccurrence (rename (liftRen ρ) b) p := by
  unfold ArgumentOccurrence at ho ⊢
  rw [subtermAt_rename, ho]
  change some (Term.var (occurrenceRenaming (liftRen ρ) p (binderDepth p))) = some (Term.var (binderDepth p))
  rw [(occurrenceRenaming_binder_iff ρ p _).mpr rfl]

def ExtractionRun.rename (ρ : Nat → Nat) (r : ExtractionRun t) : ExtractionRun (Lambda.rename ρ t) :=
  .of (r.history.rename ρ) (r.atomic.rename ρ)

def ArgumentLift.rename {R : BetaAt t p u} {σ : ParallelHistory u v} {τ : ParallelHistory t w}
    (lift : ArgumentLift R σ τ) (ρ : Nat → Nat) :
    ArgumentLift (R.rename ρ) (σ.rename ρ) (τ.rename ρ) where
  body := Lambda.rename (liftRen (occurrenceRenaming ρ p)) lift.body
  argument := Lambda.rename (occurrenceRenaming ρ p) lift.argument
  redex := by rw [subtermAt_rename, lift.redex]; rfl
  occurrence := lift.occurrence
  isVariable := lift.isVariable.rename (occurrenceRenaming ρ p)
  localPaths := lift.localPaths
  copy_paths := by rw [ParallelHistory.rename_derivation_paths]; exact lift.copy_paths
  original_paths := by rw [ParallelHistory.rename_derivation_paths]; exact lift.original_paths
  parallelization := by
    obtain ⟨z,F,full,last,row⟩ := lift.parallelization
    exact ⟨Lambda.rename ρ z,F,full.rename ρ,last.rename ρ,
      by simpa only [singleContraction_rename] using row.rename ρ⟩

theorem Internal.rename (inside : Internal site σ) (ρ : Nat → Nat) : Internal site (σ.rename ρ) := by
  intro q hq
  rw [ParallelHistory.rename_derivation_paths] at hq
  exact inside q hq

/-- Variable renaming transports every actual source generator, retaining
 its specified contraction paths and argument occurrence. -/
theorem ExtractionStep.rename (h : ExtractionStep r s) (ρ : Nat → Nat) :
    ExtractionStep (r.rename ρ) (s.rename ρ) := by
  cases h with
  | residual pre ha R S A old =>
    have renamed := ((singleContraction R).derivation.rename_residual_iff
      (singleContraction (R.rename ρ)).derivation rfl
      ⟨_,A.redex⟩ ⟨_,S.redex⟩ ⟨_,(A.rename ρ).redex⟩ ⟨_,(S.rename ρ).redex⟩ rfl rfl).mpr old
    simpa only [ExtractionRun.rename, ExtractionRun.of, ParallelHistory.rename_append,
      ParallelHistory.single, ParallelHistory.rename, singleContraction_rename] using
      ExtractionStep.residual (pre.rename ρ) (ha.rename ρ) (R.rename ρ) (S.rename ρ) (A.rename ρ) renamed
  | disjoint pre ha R σ hσ τ hτ last row positive site apart inside =>
    have projected : StepProjection (singleContraction (R.rename ρ)) (σ.rename ρ) (τ.rename ρ) (last.rename ρ) := by
      simpa only [singleContraction_rename] using row.rename ρ
    simpa only [ExtractionRun.rename, ExtractionRun.of, ParallelHistory.rename_append,
      ParallelHistory.single, ParallelHistory.rename, singleContraction_rename] using
      ExtractionStep.disjoint (pre.rename ρ) (ha.rename ρ) (R.rename ρ) (σ.rename ρ) (hσ.rename ρ)
        (τ.rename ρ) (hτ.rename ρ) (last.rename ρ) projected
        (by rw [ParallelHistory.rename_length]; exact positive) site apart (inside.rename ρ)
  | functionPart pre ha R σ hσ τ hτ last row positive inside =>
    have projected : StepProjection (singleContraction (R.rename ρ)) (σ.rename ρ) (τ.rename ρ) (last.rename ρ) := by
      simpa only [singleContraction_rename] using row.rename ρ
    simpa only [ExtractionRun.rename, ExtractionRun.of, ParallelHistory.rename_append,
      ParallelHistory.single, ParallelHistory.rename, singleContraction_rename] using
      ExtractionStep.functionPart (pre.rename ρ) (ha.rename ρ) (R.rename ρ) (σ.rename ρ) (hσ.rename ρ)
        (τ.rename ρ) (hτ.rename ρ) (last.rename ρ) projected
        (by rw [ParallelHistory.rename_length]; exact positive) (inside.rename ρ)
  | argumentPart pre ha R σ hσ τ hτ positive lift =>
    simpa only [ExtractionRun.rename, ExtractionRun.of, ParallelHistory.rename_append,
      ParallelHistory.single, ParallelHistory.rename, singleContraction_rename] using
      ExtractionStep.argumentPart (pre.rename ρ) (ha.rename ρ) (R.rename ρ) (σ.rename ρ) (hσ.rename ρ)
        (τ.rename ρ) (hτ.rename ρ) (by rw [ParallelHistory.rename_length]; exact positive) (lift.rename ρ)

theorem Extraction.rename (h : Extraction r s) (ρ : Nat → Nat) : Extraction (r.rename ρ) (s.rename ρ) := by
  induction h with
  | refl => exact .refl _
  | cons h hs ih => exact .cons (h.rename ρ) ih

theorem ExtractionJoin.rename (h : ExtractionJoin r s) (ρ : Nat → Nat) :
    ExtractionJoin (r.rename ρ) (s.rename ρ) := by
  obtain ⟨target,hr,hs⟩ := h
  exact ⟨target.rename ρ,hr.rename ρ,hs.rename ρ⟩

end Lamping.Lambda
