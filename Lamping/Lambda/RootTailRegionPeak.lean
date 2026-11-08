import Lamping.Lambda.RootDisjointTailPeak
import Lamping.Lambda.RootArgumentTailPeak
import Lamping.Lambda.ExtractionFunctionRegionLongTail
import Lamping.Lambda.ExtractionAtRoot
namespace Lamping.Lambda

/-- All earlier-root generators against a later disjoint/function generator,
 retaining the later generator's entire ordinary prefix and supplied row. -/
theorem RootExtraction.region_tail_join {R : BetaAt t p u}
    {tail : ExtractionRun u} {result : ExtractionRun t}
    (h : RootExtraction R tail result)
    (pre : ParallelHistory u a) (ha : Atomic pre) (S : BetaAt a s b)
    (lower : ParallelHistory a c) (hl : Atomic lower)
    (middle : ParallelHistory b d) (hm : Atomic middle)
    (laterRow : StepProjection (singleContraction S) lower middle laterLast)
    (positive : 0<lower.length) (region : ExtractionRegion s site)
    (inside : Internal site lower)
    (source : tail=.of ((pre.append (.single (singleContraction S))).append middle)
      ((ha.append (.single S)).append hm)) :
    ExtractionJoin result ((ExtractionRun.of (pre.append lower) (ha.append hl)).prepend
      (.single (singleContraction R)) (.single R)) := by
  have later : ExtractionStep tail (.of (pre.append lower) (ha.append hl)) := by
    rw [source]
    rcases region with apart | function
    · exact .disjoint pre ha S lower hl middle hm laterLast laterRow positive site apart inside
    · exact .functionPart pre ha S lower hl middle hm laterLast laterRow positive
        (by simpa only [function] using inside)
  cases h with
  | residual B A old =>
    have len := congrArg ExtractionRun.rank source
    have rowLength := laterRow.length
    simp only [ExtractionRun.of,ExtractionRun.rank,ParallelHistory.length_append,
      ParallelHistory.single,ParallelHistory.length] at len
    omega
  | disjoint σ hσ τ hτ last row positive' site' apart' inside' =>
    simpa only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.single,ParallelHistory.append] using
      disjoint_tail_peak R σ hσ τ hτ row positive' apart' inside' later
  | argumentPart σ hσ τ hτ positive' lift =>
    simpa only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.single,ParallelHistory.append] using
      argument_tail_peak R σ hσ τ hτ lift later
  | functionPart σ hσ τ hτ last row positive' inside' =>
    have endpoint := congrArg ExtractionRun.target source
    simp only [ExtractionRun.of] at endpoint
    cases endpoint
    have histories := hτ.paths_injective ((ha.append (.single S)).append hm)
      (congrArg (fun r => r.history.derivation.paths) source)
    cases histories
    have row' : StepProjection (singleContraction R) σ
        (pre.append (.cons (singleContraction S) middle)) last := by
      simpa only [ParallelHistory.append_assoc,ParallelHistory.single,ParallelHistory.append] using row
    simpa only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.single,ParallelHistory.append] using
      extraction_function_region_long_peak R pre ha S middle hm σ hσ row' inside'
        lower hl laterRow positive region inside

end Lamping.Lambda
