import Lamping.Lambda.FunctionRowPaths
import Lamping.Lambda.ArgumentPullback
import Lamping.Lambda.ExtractionContexts
import Lamping.Lambda.ResidualExtractionPeak
import Lamping.Lambda.FunctionArgumentOccurrenceReflect
namespace Lamping.Lambda

/-- The actual (3,4) row diagram once the specified bound-variable
 occurrence has been reflected to the old S' body. The caller must discharge
 that syntactic reflection; it is not a confluence or row certificate. -/
theorem function_argument_pullback_of_occurrence
    (R : BetaAt t p u) (S' : BetaAt t s' v) (S : BetaAt u s w) (R' : BetaAt v p w)
    (front : StepProjection (singleContraction R) (.single (singleContraction S'))
      (.single (singleContraction S)) (singleContraction R'))
    (firstInside : ∃q,s'=(p++[.fn])++q)
    (upper : ParallelHistory v upperEnd) (hu : Atomic upper)
    (copy : ParallelHistory w copyEnd) (hc : Atomic copy)
    (lower : ParallelHistory u lowerEnd) (hl : Atomic lower)
    (row : StepProjection (singleContraction R') upper copy last)
    (upperInside : Internal (p++[.fn]) upper)
    (lift : ArgumentLift S copy lower)
    (sourceLookup : subtermAt t s'=some (.app (.lam sourceBody) sourceArgument))
    (sourceOccurrence : ArgumentOccurrence sourceBody lift.occurrence) :
    ∃ (target : Term) (original : ParallelHistory t target) (_ho : Atomic original)
      (K : List Path) (vertical : ParallelStep K target lowerEnd),
      ∃ _newLift : ArgumentLift S' upper original, Internal (p++[.fn]) original ∧
      StepProjection (singleContraction R) original lower vertical := by
  have old := front.singleton_residual S' S
  obtain ⟨qs,sourceS,targetS⟩ := R.function_residual_coordinates ⟨s',S'.redex⟩ ⟨s,S.redex⟩ firstInside old
  change s'=(p++[.fn,.body])++qs at sourceS
  change s=p++qs at targetS
  have copyPaths : copy.derivation.paths=
      lift.localPaths.map (fun q => (p++(qs++lift.occurrence))++q) := by
    simpa only [targetS,List.append_assoc] using lift.copy_paths
  have upperPaths := row.function_paths_reflect_at R' hu hc upperInside copyPaths
  have upperScope : Internal (s'++lift.occurrence) upper := by
    intro name hq
    rw [upperPaths] at hq
    obtain ⟨q,_,he⟩ := List.mem_map.mp hq
    exact ⟨q,by simpa only [sourceS,List.append_assoc] using he.symm⟩
  obtain ⟨newEnd,original,ho,newLift,occEq⟩ :=
    argument_lift_exists S' sourceLookup sourceOccurrence upper upperScope
  have program : newLift.localPaths=lift.localPaths := by
    apply mapped_prefix_paths_injective (s'++lift.occurrence)
    have one : upper.derivation.paths=newLift.localPaths.map (fun q => (s'++lift.occurrence)++q) := by
      simpa only [occEq] using newLift.copy_paths
    have two : upper.derivation.paths=lift.localPaths.map (fun q => (s'++lift.occurrence)++q) := by
      simpa only [sourceS,List.append_assoc] using upperPaths
    exact one.symm.trans two
  have originalPaths : original.derivation.paths=
      lift.localPaths.map (fun q => ((p++[.fn,.body])++(qs++[.arg]))++q) := by
    simpa only [sourceS,program,List.append_assoc] using newLift.original_paths
  have originalInside : Internal (p++[.fn]) original := by
    intro name hq
    rw [originalPaths] at hq
    obtain ⟨q,_,he⟩ := List.mem_map.mp hq
    exact ⟨[.body]++qs++[.arg]++q,by simpa only [List.append_assoc] using he.symm⟩
  obtain ⟨endR,K,bottom,vertical,hb,rowR⟩ := ho.function_projection R originalInside
  have bottomPaths := rowR.function_paths_at R ho hb originalInside originalPaths
  have samePaths : bottom.derivation.paths=lower.derivation.paths := by
    rw [bottomPaths,lift.original_paths]
    simp only [targetS,List.append_assoc]
  have sameRun : ExtractionRun.of bottom hb=ExtractionRun.of lower hl := by
    apply ExtractionRun.ext_paths
    exact samePaths
  have endpoint := congrArg ExtractionRun.target sameRun
  simp only [ExtractionRun.of] at endpoint
  cases endpoint
  have histories := hb.paths_injective hl samePaths
  cases histories
  exact ⟨_,original,ho,_,vertical,newLift,originalInside,rowR⟩

/-- No occurrence-origin premise is needed: the source occurrence is
 reflected through the actual old function residual and outer substitution. -/
theorem function_argument_pullback
    (R : BetaAt t p u) (S' : BetaAt t s' v) (S : BetaAt u s w) (R' : BetaAt v p w)
    (front : StepProjection (singleContraction R) (.single (singleContraction S'))
      (.single (singleContraction S)) (singleContraction R'))
    (firstInside : ∃q,s'=(p++[.fn])++q)
    (upper : ParallelHistory v upperEnd) (hu : Atomic upper)
    (copy : ParallelHistory w copyEnd) (hc : Atomic copy)
    (lower : ParallelHistory u lowerEnd) (hl : Atomic lower)
    (row : StepProjection (singleContraction R') upper copy last)
    (upperInside : Internal (p++[.fn]) upper) (lift : ArgumentLift S copy lower) :
    ∃ (target : Term) (original : ParallelHistory t target) (_ho : Atomic original)
      (K : List Path) (vertical : ParallelStep K target lowerEnd),
      ∃ _newLift : ArgumentLift S' upper original, Internal (p++[.fn]) original ∧
      StepProjection (singleContraction R) original lower vertical := by
  obtain ⟨b',a',lookup,occurs⟩ := R.function_argument_occurrence_reflect S' S firstInside
    (front.singleton_residual S' S) lift.redex lift.isVariable
  exact function_argument_pullback_of_occurrence R S' S R' front firstInside upper hu copy hc
    lower hl row upperInside lift lookup occurs

end Lamping.Lambda
