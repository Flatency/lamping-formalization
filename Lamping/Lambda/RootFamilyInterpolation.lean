import Lamping.Lambda.PointedPrefixOperations
import Lamping.Lambda.ExtractionFamilyInvariance
import Lamping.Lambda.ExtractionAtRoot
namespace Lamping.Lambda

/-- The actual intermediate point used in AG5.4.4. Interpolation places it
 in the given projected prefix; the root extraction and genuine row then
 identify its global family. No canonical-to-Copy reflection is assumed. -/
theorem RootExtraction.family_interpolation {R : BetaAt m p u}
    {source : ExtractionRun u} {target : ExtractionRun m}
    (root : RootExtraction R source target)
    (a0 : RedexWithHistory u) (a : RedexWithHistory m) (b : RedexWithHistory u)
    (sourceRep : RunRepresents source a0) (targetRep : RunRepresents target a)
    (program : ParallelHistory u z) (last : ParallelStep F a.target z)
    (row : StepProjection (singleContraction R) a.history program last)
    (first : HistoryPrefix a0.history program) (second : HistoryPrefix program b.history)
    (copy : Copy a0 b) :
    ∃q : RedexOcc z, FamilyEq a ⟨z,a.history.append (.single last),q⟩ ∧
      Copy ⟨z,program,q⟩ b := by
  obtain ⟨q,toPoint,toTarget⟩ := first.copy_interpolation second a0.redex b.redex copy
  let intermediate : RedexWithHistory u := ⟨z,program,q⟩
  have fromSource := toPoint.prepend (.single (singleContraction R))
  have fromRoot : FamilyEq (a0.prepend (.single (singleContraction R))) a :=
    root.step.family _ a (sourceRep.prepend (.single (singleContraction R)) (.single R)) targetRep
  have shifted : Copy (intermediate.prepend (.single (singleContraction R)))
      ⟨z,a.history.append (.single last),q⟩ := by
    refine ⟨.nil _,?_,(Derivation.residual_nil q q).mpr rfl⟩
    change PermEq (((ParallelHistory.single (singleContraction R)).append program).append (.nil z))
      (a.history.append (.single last))
    rw [ParallelHistory.append_nil]
    exact row.permutation
  exact ⟨q,.trans (.symm fromRoot) (.trans (.copy fromSource) (.copy shifted)),toTarget⟩

end Lamping.Lambda
