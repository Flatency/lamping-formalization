import Lamping.Lambda.ExtractionAtRoot
import Lamping.Lambda.PointedProjectionPrefix
import Lamping.Lambda.ArgumentPointedPrefix
import Lamping.Lambda.HistoryPreorder
namespace Lamping.Lambda

/-- Every genuine root extraction projects the target pointed prefix to
an actual program extending the source pointed prefix modulo permutation.
The fourth rule retains its specified argument copy; the full projection
may also contain the other copies. -/
theorem RootExtraction.pointed_prefix_projection {R : BetaAt t p u}
    {source : ExtractionRun u} {target : ExtractionRun t}
    (root : RootExtraction R source target) (a : RedexWithHistory u) (b : RedexWithHistory t)
    (sourceRep : RunRepresents source a) (targetRep : RunRepresents target b) :
    ∃ (z : Term) (F : List Path) (program : ParallelHistory u z)
      (last : ParallelStep F b.target z),
      StepProjection (singleContraction R) b.history program last ∧
      HistoryPrefix a.history program := by
  cases root with
  | residual S A old =>
    have knownSource : RunRepresents (.of (.single (singleContraction S)) (.single S))
        ⟨u,.nil u,⟨_,S.redex⟩⟩ := ⟨S,.nil _,rfl⟩
    have knownTarget : RunRepresents (.of (.single (singleContraction A)) (.single A))
        ⟨t,.nil t,⟨_,A.redex⟩⟩ := ⟨A,.nil _,rfl⟩
    have sameSource := knownSource.unique sourceRep
    have sameTarget := knownTarget.unique targetRep
    subst a
    subst b
    exact ⟨u,[p],.nil u,singleContraction R,.nil _,HistoryPrefix.refl _⟩
  | disjoint original ho projected hp last row positive site apart inside =>
    obtain ⟨F,vertical,prefixRow⟩ := row.pointed_prefix_row ho hp sourceRep targetRep
    exact ⟨a.target,F,a.history,vertical,prefixRow,HistoryPrefix.refl _⟩
  | functionPart original ho projected hp last row positive inside =>
    obtain ⟨F,vertical,prefixRow⟩ := row.pointed_prefix_row ho hp sourceRep targetRep
    exact ⟨a.target,F,a.history,vertical,prefixRow,HistoryPrefix.refl _⟩
  | argumentPart copy hc original ho positive lift =>
    obtain ⟨prefixLift,_⟩ := lift.pointed_prefix hc ho a b sourceRep targetRep
    obtain ⟨z,F,program,last,row⟩ := StepProjection.exists_projection (singleContraction R) b.history
    have sourceAtomic := sourceRep.choose_spec.1
    have targetAtomic := targetRep.choose_spec.1
    obtain ⟨other,equivalent,_⟩ := prefixLift.factor_projection sourceAtomic targetAtomic row
    exact ⟨z,F,program,last,row,other,equivalent.symm⟩

end Lamping.Lambda
