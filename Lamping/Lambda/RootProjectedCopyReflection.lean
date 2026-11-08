import Lamping.Lambda.RootPointedProjection
import Lamping.Lambda.ArgumentPointedFiber
import Lamping.Lambda.PointedPrefixOperations
import Lamping.Lambda.ExtractionFamilyInvariance
namespace Lamping.Lambda

private theorem copy_same_history (history : ParallelHistory m t) (r s : RedexOcc t)
    (copy : Copy ⟨t,history,r⟩ ⟨t,history,s⟩) : r=s := by
  obtain ⟨extension,perm,residual⟩ := copy
  have same : PermEq (history.append extension) (history.append (.nil t)) := by
    simpa only [ParallelHistory.append_nil] using perm
  exact (Derivation.residual_nil r s).mp (((same.cancel_prefix history).residual r s).mp residual)

private theorem given_row_copy (R : BetaAt t p u)
    {top : ParallelHistory t v} {bottom : ParallelHistory u w} {last : ParallelStep F v w}
    (row : StepProjection (singleContraction R) top bottom last) (ha : Atomic top) (hb : Atomic bottom)
    (a0 : RedexWithHistory u) (a : RedexWithHistory t)
    (sourceRep : RunRepresents (.of bottom hb) a0) (targetRep : RunRepresents (.of top ha) a) :
    Copy a (a0.prepend (.single (singleContraction R))) := by
  obtain ⟨left,right,repLeft,repRight,copy⟩ := row.pointed_copy R ha hb targetRep.positive (.nil t) (.nil t)
  have sameLeft := repLeft.unique targetRep
  have sameRight := repRight.unique (sourceRep.prepend (.single (singleContraction R)) (.single R))
  subst left
  subst right
  exact copy

/-- Levy4.11's actual disjoint-remainder construction: an actual projected
prefix extends the source prefix, has one possible Copy image of its point,
and that image is also a Copy of the target point. No canonical/family
reflection principle is an input. -/
theorem RootExtraction.pointed_prefix_fiber {R : BetaAt t p u}
    {source : ExtractionRun u} {target : ExtractionRun t}
    (root : RootExtraction R source target) (a0 : RedexWithHistory u) (a : RedexWithHistory t)
    (sourceRep : RunRepresents source a0) (targetRep : RunRepresents target a) :
    ∃ (z : Term) (F : List Path) (program : ParallelHistory u z)
      (last : ParallelStep F a.target z) (q : RedexOcc z),
      StepProjection (singleContraction R) a.history program last ∧
      HistoryPrefix a0.history program ∧
      Copy a ⟨z,(ParallelHistory.single (singleContraction R)).append program,q⟩ ∧
      ∀ q' : RedexOcc z,Copy a0 ⟨z,program,q'⟩ → q'=q := by
  cases root with
  | residual S A old =>
    have knownSource : RunRepresents (.of (.single (singleContraction S)) (.single S))
        ⟨u,.nil u,⟨_,S.redex⟩⟩ := ⟨S,.nil _,rfl⟩
    have knownTarget : RunRepresents (.of (.single (singleContraction A)) (.single A))
        ⟨t,.nil t,⟨_,A.redex⟩⟩ := ⟨A,.nil _,rfl⟩
    have sameSource := knownSource.unique sourceRep
    have sameTarget := knownTarget.unique targetRep
    subst a0
    subst a
    refine ⟨u,[p],.nil u,singleContraction R,⟨_,S.redex⟩,.nil _,HistoryPrefix.refl _,?_,?_⟩
    · exact ⟨.single (singleContraction R),.refl _,by
        simpa only [ParallelHistory.single_derivation] using old⟩
    · intro q' copy
      exact (copy_same_history (.nil u) _ q' copy).symm
  | disjoint original ho projected hp last row positive site apart inside =>
    obtain ⟨F,vertical,prefixRow⟩ := row.pointed_prefix_row ho hp sourceRep targetRep
    have copy := given_row_copy R row ho hp a0 a sourceRep targetRep
    refine ⟨a0.target,F,a0.history,vertical,a0.redex,prefixRow,HistoryPrefix.refl _,copy,?_⟩
    intro q' copied
    exact (copy_same_history a0.history a0.redex q' copied).symm
  | functionPart original ho projected hp last row positive inside =>
    obtain ⟨F,vertical,prefixRow⟩ := row.pointed_prefix_row ho hp sourceRep targetRep
    have copy := given_row_copy R row ho hp a0 a sourceRep targetRep
    refine ⟨a0.target,F,a0.history,vertical,a0.redex,prefixRow,HistoryPrefix.refl _,copy,?_⟩
    intro q' copied
    exact (copy_same_history a0.history a0.redex q' copied).symm
  | argumentPart copy hc original ho positive lift =>
    obtain ⟨program,lastPath,copyPaths,originalPaths,copyLast,originalLast⟩ :=
      lift.pointed_coordinates hc ho a0 a sourceRep targetRep
    have sourceAtomic := sourceRep.choose_spec.1
    have targetAtomic := targetRep.choose_spec.1
    obtain ⟨z,F,full,last,row⟩ := StepProjection.exists_projection (singleContraction R) a.history
    obtain ⟨q,copied,unique⟩ := argument_pointed_projection_fiber R lift.redex lift.isVariable
      a.history targetAtomic a0.history sourceAtomic program originalPaths copyPaths
      a.redex a0.redex originalLast copyLast row
    obtain ⟨other,factor,_⟩ := targetAtomic.argument_projection_factor (singleContraction R) rfl
      lift.redex lift.isVariable program originalPaths sourceAtomic copyPaths row
    exact ⟨z,F,full,last,q,row,⟨other,factor.symm⟩,copied,unique⟩

end Lamping.Lambda
