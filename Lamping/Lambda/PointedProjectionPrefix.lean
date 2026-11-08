import Lamping.Lambda.ProjectionFamilies
namespace Lamping.Lambda

/-- Removing the actual final beta from both ordinary sides of a given
row retains an actual projection row between their pointed prefixes. -/
theorem StepProjection.pointed_prefix_row {step : ParallelStep F t u}
    {top : ParallelHistory t v} {bottom : ParallelHistory u w} {last : ParallelStep G v w}
    (row : StepProjection step top bottom last) (ha : Atomic top) (hb : Atomic bottom)
    {a : RedexWithHistory u} {b : RedexWithHistory t}
    (sourceRep : RunRepresents (.of bottom hb) a)
    (targetRep : RunRepresents (.of top ha) b) :
    ∃ K,∃ vertical : ParallelStep K b.target a.target,
      StepProjection step b.history a.history vertical := by
  obtain ⟨lastB,_,topEq⟩ := targetRep
  change top=b.history.append (.single (singleContraction lastB)) at topEq
  rw [topEq] at row
  obtain ⟨middle,K,program,vertical,tail,prefixRow,bottomEq⟩ :=
    row.split_last b.history (singleContraction lastB)
  have atomic : Atomic (program.append (.single tail)) := by rw [←bottomEq]; exact hb
  obtain ⟨prefixAtomic,tailAtomic⟩ := atomic.split_append
  obtain ⟨q,T,paths⟩ := tailAtomic.single_step
  have tailEq : ParallelHistory.single tail=.single (singleContraction T) :=
    tailAtomic.paths_injective (.single T) (by
      simpa only [ParallelHistory.single_derivation] using paths)
  let point : RedexWithHistory u := ⟨middle,program,⟨q,T.redex⟩⟩
  have represents : RunRepresents (.of bottom hb) point :=
    ⟨T,prefixAtomic,bottomEq.trans (congrArg (program.append ·) tailEq)⟩
  have equal := represents.unique sourceRep
  subst a
  exact ⟨K,vertical,prefixRow⟩

end Lamping.Lambda
