import Lamping.Lambda.RootTailRegionPeak
import Lamping.Lambda.ExtractionFunctionArgumentLongTail
namespace Lamping.Lambda

/-- The remaining later-(iv) column, including arbitrary ordinary prefixes. -/
theorem RootExtraction.argument_tail_join {R : BetaAt t p u}
    {tail : ExtractionRun u} {result : ExtractionRun t}
    (h : RootExtraction R tail result)
    (pre : ParallelHistory u a) (ha : Atomic pre) (S : BetaAt a s b)
    (copy : ParallelHistory b c) (hc : Atomic copy)
    (original : ParallelHistory a d) (ho : Atomic original)
    (positive : 0<copy.length) (lift : ArgumentLift S copy original)
    (source : tail=.of ((pre.append (.single (singleContraction S))).append copy)
      ((ha.append (.single S)).append hc)) :
    ExtractionJoin result ((ExtractionRun.of (pre.append original) (ha.append ho)).prepend
      (.single (singleContraction R)) (.single R)) := by
  have later : ExtractionStep tail (.of (pre.append original) (ha.append ho)) := by
    rw [source]
    exact .argumentPart pre ha S copy hc original ho positive lift
  cases h with
  | residual B A old =>
    have len := congrArg ExtractionRun.rank source
    simp only [ExtractionRun.of,ExtractionRun.rank,ParallelHistory.length_append,
      ParallelHistory.single,ParallelHistory.length] at len
    omega
  | disjoint σ hσ τ hτ last row positive' site' apart' inside' =>
    simpa only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.single,ParallelHistory.append] using
      disjoint_tail_peak R σ hσ τ hτ row positive' apart' inside' later
  | argumentPart σ hσ τ hτ positive' lift' =>
    simpa only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.single,ParallelHistory.append] using
      argument_tail_peak R σ hσ τ hτ lift' later
  | functionPart σ hσ τ hτ last row positive' inside' =>
    have endpoint := congrArg ExtractionRun.target source
    simp only [ExtractionRun.of] at endpoint
    cases endpoint
    have histories := hτ.paths_injective ((ha.append (.single S)).append hc)
      (congrArg (fun r => r.history.derivation.paths) source)
    cases histories
    have row' : StepProjection (singleContraction R) σ
        (pre.append (.cons (singleContraction S) copy)) last := by
      simpa only [ParallelHistory.append_assoc,ParallelHistory.single,ParallelHistory.append] using row
    simpa only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.single,ParallelHistory.append] using
      extraction_function_argument_long_peak R pre ha S copy hc σ hσ row' inside'
        original ho positive lift

end Lamping.Lambda
