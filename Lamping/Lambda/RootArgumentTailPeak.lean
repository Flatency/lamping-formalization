import Lamping.Lambda.ExtractionMirror
import Lamping.Lambda.ArgumentLiftSplits
import Lamping.Lambda.ExtractionInternal
import Lamping.Lambda.ArgumentPullback
namespace Lamping.Lambda

/-- An arbitrary actual extraction in the designated argument instance can
 be transported to the original argument. This treats all four later rules,
 including their ordinary prefixes, by context and shift reflection. -/
theorem argument_tail_peak (R : BetaAt t p u)
    (copy : ParallelHistory u v) (hc : Atomic copy)
    (original : ParallelHistory t w) (ho : Atomic original)
    (lift : ArgumentLift R copy original) {result : ExtractionRun u}
    (later : ExtractionStep (.of copy hc) result) :
    ExtractionJoin (.of original ho)
      (.of (.cons (singleContraction R) result.history) (.cons R result.atomic)) := by
  rcases lift with ⟨body,argument,redex,occurrence,isVariable,localPaths,copyPaths,originalPaths,parallelization⟩
  let lift : ArgumentLift R copy original :=
    ⟨body,argument,redex,occurrence,isVariable,localPaths,copyPaths,originalPaths,parallelization⟩
  have argumentLookup : subtermAt t (p++[.arg])=some lift.argument := by
    rw [subtermAt_append,lift.redex]
    cases argument <;> rfl
  have copyLookup : subtermAt u (p++lift.occurrence)=
      some (rename (fun i => i+binderDepth lift.occurrence) lift.argument) := by
    rw [subtermAt_append,R.contract_lookup lift.redex,Option.bind_some]
    exact argument_copy lift.isVariable lift.argument
  obtain ⟨C,cp,ct⟩ := SyntaxContext.of_lookup argumentLookup
  obtain ⟨D,dp,dt⟩ := SyntaxContext.of_lookup copyLookup
  change C.plug argument=t at ct
  change D.plug (rename (fun i => i+binderDepth occurrence) argument)=u at dt
  cases ct
  cases dt
  obtain ⟨a,localOriginal,hoa,endpointO,heO,pathsO⟩ :=
    C.reflectHistory original ho (by simpa only [cp] using lift.original_internal)
  obtain ⟨b,localCopy,hcb,endpointC,heC,pathsC⟩ :=
    D.reflectHistory copy hc (by simpa only [dp] using lift.copy_internal)
  let ro : ExtractionRun lift.argument := .of localOriginal hoa
  let rc : ExtractionRun (rename (fun i => i+binderDepth lift.occurrence) lift.argument) :=
    .of localCopy hcb
  have localOriginalPaths : localOriginal.derivation.paths=lift.localPaths := by
    apply mapped_prefix_paths_injective (p++[.arg])
    rw [←cp,←pathsO]
    simpa only [cp] using lift.original_paths
  have localCopyPaths : localCopy.derivation.paths=lift.localPaths := by
    apply mapped_prefix_paths_injective (p++lift.occurrence)
    rw [←dp,←pathsC]
    simpa only [dp] using lift.copy_paths
  have copyRenamed : rc=ro.rename (fun i => i+binderDepth lift.occurrence) := by
    apply ExtractionRun.ext_paths
    simp only [ExtractionRun.rename_paths,ro,rc,ExtractionRun.of]
    exact localCopyPaths.trans localOriginalPaths.symm
  have actualOriginal : ExtractionRun.of original ho=C.liftRun ro := by
    apply ExtractionRun.ext_paths
    rw [C.liftRun_paths]
    exact pathsO
  have actualCopy : ExtractionRun.of copy hc=D.liftRun rc := by
    apply ExtractionRun.ext_paths
    rw [D.liftRun_paths]
    exact pathsC
  rw [actualCopy] at later
  obtain ⟨localResult,localStep,targetCopy⟩ := D.reflectExtractionStep later
  rw [copyRenamed] at localStep
  obtain ⟨q,qstep,shiftEq⟩ := localStep.shift_reflect (binderDepth lift.occurrence)
  rw [shiftEq] at targetCopy
  have originalStep : ExtractionStep (.of original ho) (C.liftRun q) := by
    rw [actualOriginal]
    exact C.liftExtractionStep qstep
  have resultInside : Internal (p++lift.occurrence) result.history := by
    apply later.internal
    rw [←actualCopy]
    exact lift.copy_internal
  obtain ⟨newTarget,newOriginal,newAtomic,newLift,occEq⟩ :=
    argument_lift_exists R lift.redex lift.isVariable result.history resultInside
  have newPaths : newLift.localPaths=q.history.derivation.paths := by
    apply mapped_prefix_paths_injective (p++lift.occurrence)
    have copyNames : result.history.derivation.paths=
        newLift.localPaths.map (fun q => (p++lift.occurrence)++q) := by
      simpa only [occEq] using newLift.copy_paths
    have targetNames := congrArg (fun r => r.history.derivation.paths) targetCopy
    simp only [D.liftRun_paths,ExtractionRun.rename_paths,dp] at targetNames
    exact copyNames.symm.trans targetNames
  have sameOriginal : ExtractionRun.of newOriginal newAtomic=C.liftRun q := by
    apply ExtractionRun.ext_paths
    change newOriginal.derivation.paths=(C.liftRun q).history.derivation.paths
    rw [C.liftRun_paths,newLift.original_paths,newPaths,cp]
  have copyPositive : 0<result.history.length := by
    exact later.positive
  have rootStep : ExtractionStep
      (.of (.cons (singleContraction R) result.history) (.cons R result.atomic))
      (.of newOriginal newAtomic) := by
    exact ExtractionStep.argumentPart (.nil _) (.nil _) R _ result.atomic
      _ newAtomic copyPositive newLift
  refine ⟨C.liftRun q,Extraction.single originalStep,Extraction.single ?_⟩
  rw [sameOriginal] at rootStep
  exact rootStep

end Lamping.Lambda
