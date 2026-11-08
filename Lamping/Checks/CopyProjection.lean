import Lamping.Lambda.CopyProjection
import Lamping.Lambda.ArgumentResidualScope
import Lamping.Lambda.CopyRegionAncestry
import Lamping.Lambda.CopyRegionProjection
namespace Lamping.Checks.CopyProjection
open Lambda
abbrev delta : Term := .lam (.app (.var 0) (.var 0))
abbrev omegaTerm : Term := .app delta delta
abbrev original : Term := .app (.lam (.app (.var 0) (.var 0))) omegaTerm
abbrev twins : Term := .app omegaTerm omegaTerm
def duplicate : BetaAt original [] twins := ⟨.app (.var 0) (.var 0),omegaTerm,rfl,rfl⟩
def omegaBeta : BetaAt omegaTerm [] omegaTerm := ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
def argumentRedex : RedexOcc original := ⟨[.arg],omegaBeta.redex⟩
def leftRedex : RedexOcc twins := ⟨[.fn],omegaBeta.redex⟩
/-- A real nonlinear root duplicates the source argument identity. The
rectangle chooses the left image required by this target pointed history. -/
example : ∃ image : RedexOcc twins, image.val=[.fn] ∧
    (singleContraction duplicate).derivation.Residual argumentRedex image ∧
    Copy ⟨twins,.nil twins,image⟩ ⟨twins,.nil twins,leftRedex⟩ := by
  let a : RedexWithHistory original := ⟨original,.nil original,argumentRedex⟩
  let b : RedexWithHistory twins := ⟨twins,.nil twins,leftRedex⟩
  have residual : (singleContraction duplicate).derivation.Residual argumentRedex leftRedex :=
    (duplicate.argument_residual_iff rfl argumentRedex (q:=[]) rfl leftRedex).mpr ⟨[.fn],rfl,rfl⟩
  have copy : Copy a ⟨b.target,(ParallelHistory.single (singleContraction duplicate)).append b.history,b.redex⟩ :=
    ⟨.single (singleContraction duplicate),.refl _,residual⟩
  obtain ⟨image,oldImage,copyImage⟩ := copy.project_target_head duplicate a b (.nil (singleContraction duplicate))
  have alive := (copyImage.initial_residual image).mp ((Derivation.residual_nil image image).mpr rfl)
  have same : image=leftRedex := (Derivation.residual_nil image leftRedex).mp alive
  exact ⟨image,congrArg Subtype.val same,oldImage,copyImage⟩
#print axioms StepProjection.self_beta_head_last_empty
#print axioms Copy.project_target_head
example {r s : ExtractionRun m} (steps : Pruning r s) (a b : RedexWithHistory m)
    (source : RunRepresents r a) (target : RunRepresents s b) : Copy b a := steps.copy a b source target
#print axioms PruningStep.copy
#print axioms Pruning.copy
#print axioms Pruning.extraction
def rightStep : BetaAt twins [.arg] twins := ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
def leftStep : BetaAt twins [.fn] twins := ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
example : ∃ w, ∃ source : ParallelHistory twins w, ∃ ordinary : Atomic source,
    source.derivation.paths=[[.fn]] ∧ Internal [.fn] source ∧
    Pruning (.of ((ParallelHistory.single (singleContraction rightStep)).append (.single (singleContraction leftStep)))
      ((Atomic.single rightStep).append (.single leftStep))) (.of source ordinary) := by
  apply (Atomic.single rightStep).prune_disjoint_prefix (.single (singleContraction leftStep)) (.single leftStep)
  · intro p hp
    have eq : p=[.fn] := by simpa [ParallelHistory.single_derivation,ParallelStep.derivation,singleContraction] using hp
    exact ⟨[],eq⟩
  · decide
  · intro p hp
    have eq : p=[.arg] := by simpa [ParallelHistory.single_derivation,ParallelStep.derivation,singleContraction] using hp
    rw [eq]
    exact DisjointPositions.head_ne (by intro eq; cases eq)
#print axioms Atomic.prune_initial_residual
#print axioms Atomic.prune_apart_suffix
#print axioms Atomic.prune_disjoint_prefix
#print axioms ProtectedBlocks.prune_function_pointed
#print axioms ProtectedBlocks.prune_argument_pointed
#print axioms Atomic.prune_local_program
#print axioms RightHistory.prune_right_pointed
#print axioms Copy.project_region_run
end Lamping.Checks.CopyProjection
