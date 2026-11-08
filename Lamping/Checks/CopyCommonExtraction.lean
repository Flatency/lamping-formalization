import Lamping.Lambda.CopyCommonExtraction
namespace Lamping.Checks.CopyCommonExtraction
open Lambda
abbrev delta : Term := .lam (.app (.var 0) (.var 0))
abbrev omegaTerm : Term := .app delta delta
abbrev twins : Term := .app omegaTerm omegaTerm
def rightBeta : BetaAt twins [.arg] twins := ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
def leftBeta : BetaAt twins [.fn] twins := ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
def nonstandardFull : ExtractionRun twins := .of
  (.cons (singleContraction rightBeta) (.single (singleContraction leftBeta))) (.cons rightBeta (.single leftBeta))
theorem nonstandardFull_not_standard : ¬Standard nonstandardFull.history := by
  intro standard
  have inside := (Atomic.single leftBeta).app_arg_stays rightBeta
    (by intro p hp; change p∈[[.arg],[.fn]] at hp; simp only [List.mem_cons,List.not_mem_nil,or_false] at hp; rcases hp with rfl | rfl <;> simp) standard
  obtain ⟨q,eq⟩ := inside [.fn] (by simp [ParallelHistory.derivation,Derivation.append,ParallelStep.derivation,singleContraction])
  cases eq
/-- The new general theorem genuinely accepts a nonstandard full pointed
run, because its one-beta pointed prefix is standard. -/
example : ExtractionJoin nonstandardFull nonstandardFull ∧ ¬Standard nonstandardFull.history := by
  let a : RedexWithHistory twins := ⟨twins,.single (singleContraction rightBeta),⟨[.fn],leftBeta.redex⟩⟩
  have represented : RunRepresents nonstandardFull a := ⟨leftBeta,.single rightBeta,rfl⟩
  have standard : Standard a.history := Standard.single_step _ ⟨[.arg],rightBeta.redex⟩ (leftmost_singleton _)
  exact ⟨(Copy.refl a).standard_common_extraction represented represented standard standard,nonstandardFull_not_standard⟩

abbrev functionSource : Term := .app (.lam twins) (.var 0)
def outer : BetaAt functionSource [] twins := ⟨twins,.var 0,rfl,rfl⟩
def internalLeft : BetaAt functionSource [.fn,.body,.fn] functionSource :=
  ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
def internalRight : BetaAt functionSource [.fn,.body,.arg] functionSource :=
  ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
def sourcePoint : RedexWithHistory functionSource :=
  ⟨functionSource,.single (singleContraction internalLeft),⟨[.fn,.body,.arg],internalRight.redex⟩⟩
def targetPoint : RedexWithHistory functionSource :=
  ⟨twins,(ParallelHistory.single (singleContraction outer)).append (.single (singleContraction leftBeta)),⟨[.arg],rightBeta.redex⟩⟩
def functionRun : ExtractionRun functionSource :=
  .of ((ParallelHistory.single (singleContraction internalLeft)).append (.single (singleContraction internalRight)))
    ((Atomic.single internalLeft).append (.single internalRight))
def projectedRun : ExtractionRun functionSource :=
  .of (targetPoint.history.append (.single (singleContraction rightBeta)))
    (((Atomic.single outer).append (.single leftBeta)).append (.single rightBeta))
/-- Both pointed prefixes are nonempty and have different first betas. The
source is in the function region of the target's first outer contraction. -/
example : ExtractionJoin functionRun projectedRun := by
  have firstNames : (singleContraction outer).residualSet [[.fn,.body,.fn]]=[[.fn]] := by decide
  have secondNames : (singleContraction internalLeft).residualSet [[]]=[[]] := by decide
  let square : ParallelMovesSquare [[]] [[.fn,.body,.fn]] functionSource twins functionSource twins :=
    ⟨singleContraction outer,singleContraction internalLeft,
      firstNames.symm ▸ singleContraction leftBeta,secondNames.symm ▸ singleContraction outer⟩
  have perm : PermEq ((ParallelHistory.single (singleContraction internalLeft)).append (.single (singleContraction outer)))
      targetPoint.history := by
    have generated := (PermEq.moves square).symm
    simpa only [square,ParallelHistory.cons_selection_cast] using generated
  have residual : (singleContraction outer).derivation.Residual sourcePoint.redex targetPoint.redex :=
    ((singleContraction outer).residual_iff sourcePoint.redex targetPoint.redex).mpr (by decide)
  have copy : Copy sourcePoint targetPoint := ⟨.single (singleContraction outer),perm,by
    simpa only [ParallelHistory.single_derivation] using residual⟩
  have sourceStandard : Standard sourcePoint.history :=
    Standard.single_step _ ⟨[.fn,.body,.fn],internalLeft.redex⟩ (leftmost_singleton _)
  have targetStandard : Standard targetPoint.history := by
    refine .cons (singleContraction outer) ⟨[],outer.redex⟩ (leftmost_singleton _) ?_
      (Standard.single_step _ ⟨[.fn],leftBeta.redex⟩ (leftmost_singleton _))
    intro old earlier
    change LeftOf old.val [] at earlier
    have impossible : ∀p : Path,¬LeftOf p [] := by intro p h; cases h
    exfalso
    exact impossible old.val earlier
  exact copy.standard_common_extraction ⟨internalRight,.single internalLeft,rfl⟩
    ⟨rightBeta,(Atomic.single outer).append (.single leftBeta),rfl⟩ sourceStandard targetStandard
#print axioms RedexOcc.after_regions
#print axioms Atomic.copy_standard_join
#print axioms Copy.standard_common_extraction
end Lamping.Checks.CopyCommonExtraction

