import Lamping.Lambda.DisjointRowPaths
import Lamping.Lambda.DisjointHistoryPullback
import Lamping.Lambda.ExtractionContextReflect
namespace Lamping.Lambda

private theorem internal_source_lookup {σ : ParallelHistory t u} (ha : Atomic σ) (positive : 0<σ.length)
    (inside : Internal site σ) : ∃a,subtermAt t site=some a := by
  cases ha with
  | nil => simp only [ParallelHistory.length] at positive; omega
  | cons A ht =>
    have scope := inside _ (by change (_ : Path)∈_::_; exact List.mem_cons_self)
    obtain ⟨q,hq⟩ := scope
    obtain ⟨redex,hr,_⟩ := A.redex
    rw [hq] at hr
    obtain ⟨a,ha,_⟩ := prefix_exists hr
    exact ⟨a,ha⟩

/-- A disjoint source extraction commutes with any later extraction inside
 its ordinary projected run, including all four generators and prefixes. -/
theorem disjoint_tail_peak (R : BetaAt t p u)
    (original : ParallelHistory t v) (ho : Atomic original)
    (projected : ParallelHistory u w) (hp : Atomic projected)
    (row : StepProjection (singleContraction R) original projected last)
    (positive : 0<original.length) (apart : DisjointPositions p site)
    (inside : Internal site original) {result : ExtractionRun u}
    (later : ExtractionStep (.of projected hp) result) :
    ExtractionJoin (.of original ho)
      (.of (.cons (singleContraction R) result.history) (.cons R result.atomic)) := by
  have samePaths := row.disjoint_paths R ho hp apart inside
  have projectedInside : Internal site projected := by
    intro q hq
    exact inside q (samePaths ▸ hq)
  obtain ⟨a,lookup⟩ := internal_source_lookup ho positive inside
  have lookup' : subtermAt u site=some a := (R.disjoint_subterm apart).trans lookup
  obtain ⟨C,cp,ct⟩ := SyntaxContext.of_lookup lookup
  obtain ⟨D,dp,dt⟩ := SyntaxContext.of_lookup lookup'
  cases ct
  cases dt
  obtain ⟨b,localOriginal,hoa,endpointO,heO,pathsO⟩ :=
    C.reflectHistory original ho (by simpa only [cp] using inside)
  obtain ⟨c,localProjected,hpc,endpointP,heP,pathsP⟩ :=
    D.reflectHistory projected hp (by simpa only [dp] using projectedInside)
  let ro : ExtractionRun a := .of localOriginal hoa
  let rp : ExtractionRun a := .of localProjected hpc
  have localSame : rp=ro := by
    apply ExtractionRun.ext_paths
    apply mapped_prefix_paths_injective site
    change localProjected.derivation.paths.map (fun q => site++q)=
      localOriginal.derivation.paths.map (fun q => site++q)
    rw [←dp,←pathsP,dp,←cp,←pathsO]
    exact samePaths.symm
  have actualOriginal : ExtractionRun.of original ho=C.liftRun ro := by
    apply ExtractionRun.ext_paths
    rw [C.liftRun_paths]
    exact pathsO
  have actualProjected : ExtractionRun.of projected hp=D.liftRun rp := by
    apply ExtractionRun.ext_paths
    rw [D.liftRun_paths]
    exact pathsP
  rw [actualProjected] at later
  obtain ⟨q,qstep,target⟩ := D.reflectExtractionStep later
  rw [localSame] at qstep
  have originalStep : ExtractionStep (.of original ho) (C.liftRun q) := by
    rw [actualOriginal]
    exact C.liftExtractionStep qstep
  have resultInside : Internal site result.history := by
    apply later.internal
    rw [←actualProjected]
    exact projectedInside
  obtain ⟨z,source,remaining,hs,sourcePaths,sourceInside,sourceRow⟩ :=
    result.atomic.disjoint_row_pullback R apart resultInside
  have sameSource : ExtractionRun.of source hs=C.liftRun q := by
    apply ExtractionRun.ext_paths
    change source.derivation.paths=(C.liftRun q).history.derivation.paths
    have targetPaths := congrArg (fun r => r.history.derivation.paths) target
    simp only [D.liftRun_paths,dp] at targetPaths
    rw [sourcePaths,targetPaths,C.liftRun_paths,cp]
  have sourcePositive : 0<source.length := by
    have len := sourceRow.length
    have pos : 0<result.history.length := later.positive
    omega
  have rootStep : ExtractionStep
      (.of (.cons (singleContraction R) result.history) (.cons R result.atomic))
      (.of source hs) :=
    ExtractionStep.disjoint (.nil _) (.nil _) R source hs
      result.history result.atomic (singleContraction remaining) sourceRow sourcePositive site apart sourceInside
  rw [sameSource] at rootStep
  exact ⟨C.liftRun q,Extraction.single originalStep,Extraction.single rootStep⟩

end Lamping.Lambda
