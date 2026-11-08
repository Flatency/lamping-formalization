import Lamping.Lambda.CopyArgumentProjection
namespace Lamping.Checks.CopyArgumentProjection
open Lambda
abbrev delta : Term := .lam (.app (.var 0) (.var 0))
abbrev omegaTerm : Term := .app delta delta
abbrev original : Term := .app (.lam (.app (.var 0) (.var 0))) omegaTerm
abbrev twins : Term := .app omegaTerm omegaTerm
def duplicate : BetaAt original [] twins := ⟨.app (.var 0) (.var 0),omegaTerm,rfl,rfl⟩
def omegaBeta : BetaAt omegaTerm [] omegaTerm := ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
def argumentBeta : BetaAt original [.arg] original := ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
def leftBeta : BetaAt twins [.fn] twins := ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
def argumentRedex : RedexOcc original := ⟨[.arg],omegaBeta.redex⟩
def rightRedex : RedexOcc twins := ⟨[.arg],omegaBeta.redex⟩
def source : RedexWithHistory original := ⟨original,.nil original,argumentRedex⟩
def target : RedexWithHistory twins := ⟨twins,.single (singleContraction leftBeta),rightRedex⟩
/-- After one left-copy contraction, the original argument's old identity
survives in the other copy. The new bridge chooses a genuine ordinary copy
and supplies the rule (iv) extraction, rather than assuming direct Copy
between arbitrary original/copy pointed histories. -/
example : ∃ s : ExtractionRun twins, ∃ image : RedexWithHistory twins,
    RunRepresents s image ∧ Standard image.history ∧ Copy image target ∧
    Extraction (s.prepend (.single (singleContraction duplicate)) (.single duplicate))
      (.of (.single (singleContraction argumentBeta)) (.single argumentBeta)) := by
  have first : (singleContraction duplicate).derivation.Residual argumentRedex rightRedex :=
    (duplicate.argument_residual_iff rfl argumentRedex (q:=[]) rfl rightRedex).mpr ⟨[.arg],rfl,rfl⟩
  have second : (singleContraction leftBeta).derivation.Residual rightRedex rightRedex :=
    (leftBeta.disjoint_residual_iff rightRedex (DisjointPositions.head_ne (by intro eq; cases eq)) rightRedex).mpr rfl
  have copy : Copy source ⟨target.target,(ParallelHistory.single (singleContraction duplicate)).append target.history,target.redex⟩ := by
    refine ⟨(ParallelHistory.single (singleContraction duplicate)).append (.single (singleContraction leftBeta)),.refl _,?_⟩
    rw [ParallelHistory.derivation_append,ParallelHistory.single_derivation,ParallelHistory.single_derivation,Derivation.residual_append]
    exact ⟨rightRedex,first,second⟩
  apply copy.project_argument_run duplicate source target
  · exact ⟨argumentBeta,.nil _,rfl⟩
  · exact .nil _
  · intro p hp
    have eq : p=[.arg] := by simpa [ExtractionRun.of,ParallelHistory.single_derivation,ParallelStep.derivation,singleContraction] using hp
    exact ⟨[],eq⟩
#print axioms Atomic.argument_forward_mirror
#print axioms Copy.project_argument_run
end Lamping.Checks.CopyArgumentProjection

