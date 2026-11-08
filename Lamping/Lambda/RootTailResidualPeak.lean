import Lamping.Lambda.ExtractionCuts
import Lamping.Lambda.ExtractionFunctionLongTail
import Lamping.Lambda.ExtractionDisjointLongTail
import Lamping.Lambda.ExtractionArgumentLongTail
namespace Lamping.Lambda

/-- The complete earlier-root/later-(i) matrix. The earlier generator may
 be any of the four source rules and the later residual deletion may follow
 an arbitrary ordinary middle history. -/
theorem RootExtraction.residual_tail_join {R : BetaAt t p u}
    {tail : ExtractionRun u} {result : ExtractionRun t}
    (h : RootExtraction R tail result)
    (pre : ParallelHistory u a) (ha : Atomic pre)
    (S : BetaAt a s b) (T : BetaAt b z c) (V : BetaAt a q d)
    (old : (singleContraction S).derivation.Residual ⟨q,V.redex⟩ ⟨z,T.redex⟩)
    (source : tail = .of ((pre.append (.single (singleContraction S))).append
      (.single (singleContraction T))) ((ha.append (.single S)).append (.single T))) :
    ExtractionJoin result ((ExtractionRun.of (pre.append (.single (singleContraction V)))
      (ha.append (.single V))).prepend (.single (singleContraction R)) (.single R)) := by
  cases h with
  | residual B A old' =>
    have len := congrArg ExtractionRun.rank source
    simp only [ExtractionRun.of, ExtractionRun.rank, ParallelHistory.length_append,
      ParallelHistory.single, ParallelHistory.length] at len
    omega
  | disjoint σ hσ τ hτ last row positive site apart inside =>
    have endpoint := congrArg ExtractionRun.target source
    simp only [ExtractionRun.of] at endpoint
    cases endpoint
    have histories := hτ.paths_injective ((ha.append (.single S)).append (.single T))
      (congrArg (fun r => r.history.derivation.paths) source)
    cases histories
    have row' : StepProjection (singleContraction R) σ
        (pre.append (.cons (singleContraction S) (.single (singleContraction T)))) last := by
      simpa only [ParallelHistory.append_assoc, ParallelHistory.single, ParallelHistory.append] using row
    exact extraction_disjoint_residual_long_peak R pre ha S T σ hσ row' apart inside V old
  | functionPart σ hσ τ hτ last row positive inside =>
    have endpoint := congrArg ExtractionRun.target source
    simp only [ExtractionRun.of] at endpoint
    cases endpoint
    have histories := hτ.paths_injective ((ha.append (.single S)).append (.single T))
      (congrArg (fun r => r.history.derivation.paths) source)
    cases histories
    have row' : StepProjection (singleContraction R) σ
        (pre.append (.cons (singleContraction S) (.single (singleContraction T)))) last := by
      simpa only [ParallelHistory.append_assoc, ParallelHistory.single, ParallelHistory.append] using row
    exact extraction_function_residual_long_peak R pre ha S T σ hσ row' inside V old
  | argumentPart σ hσ τ hτ positive lift =>
    have endpoint := congrArg ExtractionRun.target source
    simp only [ExtractionRun.of] at endpoint
    cases endpoint
    have histories := hσ.paths_injective ((ha.append (.single S)).append (.single T))
      (congrArg (fun r => r.history.derivation.paths) source)
    cases histories
    have lift' : ArgumentLift R
        (pre.append (.cons (singleContraction S) (.single (singleContraction T)))) τ := by
      simpa only [ParallelHistory.append_assoc, ParallelHistory.single, ParallelHistory.append] using lift
    exact extraction_argument_residual_long_peak R pre ha S T τ hτ lift' V old

end Lamping.Lambda
