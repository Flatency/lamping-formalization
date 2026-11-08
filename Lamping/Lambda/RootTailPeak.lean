import Lamping.Lambda.RootTailArgumentPeak
import Lamping.Lambda.RootTailResidualPeak
namespace Lamping.Lambda

/-- Every root deletion commutes with every actual later deletion, including
 its full ordinary prefix. All sixteen kinds use the original generators. -/
theorem RootExtraction.tail_join {R : BetaAt t p u}
    {tail next : ExtractionRun u} {result : ExtractionRun t}
    (root : RootExtraction R tail result) (later : ExtractionStep tail next) :
    ExtractionJoin result (next.prepend (.single (singleContraction R)) (.single R)) := by
  cases later with
  | residual pre ha S T V old => exact root.residual_tail_join pre ha S T V old rfl
  | disjoint pre ha S lower hl middle hm last row positive site apart inside =>
    exact root.region_tail_join pre ha S lower hl middle hm row positive (.inl apart) inside rfl
  | functionPart pre ha S lower hl middle hm last row positive inside =>
    exact root.region_tail_join pre ha S lower hl middle hm row positive (.inr rfl) inside rfl
  | argumentPart pre ha S copy hc original ho positive lift =>
    exact root.argument_tail_join pre ha S copy hc original ho positive lift rfl

end Lamping.Lambda
