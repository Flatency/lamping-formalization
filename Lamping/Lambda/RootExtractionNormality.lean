import Lamping.Lambda.DisjointNormalReflection
import Lamping.Lambda.FunctionNormalReflection
namespace Lamping.Lambda

/-- A single root extraction from an already normal tail produces a normal
 target. Each of the four original rules is reflected through its actual
 local context, substitution, or specified argument copy. -/
theorem RootExtraction.normal_target {R : BetaAt t p u}
    (root : RootExtraction R tail result) (normal : ExtractionNormal tail) :
    ExtractionNormal result := by
  cases root with
  | residual S A old => exact extraction_single_normal A
  | disjoint original ho projected hp last row positive site apart inside =>
    exact row.disjoint_normal_reflect R ho hp positive apart inside normal
  | functionPart original ho projected hp last row positive inside =>
    exact row.function_normal_reflect R ho hp inside normal
  | argumentPart copy hc original ho positive lift => exact lift.normal_original hc ho normal

end Lamping.Lambda
