import Lamping.Lambda.FunctionResidualGeometry
import Lamping.Lambda.ExtractionFunctionResidualPeak
import Lamping.Lambda.ExtractionInternal
namespace Lamping.Lambda

/-- LEV80 (3,2)/(3,3) for the actual three-contraction core. The later
 region's single contraction is pulled back to the function body, where
 disjointness or function containment is reconstructed from old coordinates. -/
theorem extraction_function_region_peak
    (R : BetaAt t p u) (S : BetaAt u s v) (T : BetaAt v z w)
    (S' : BetaAt t s' v') (T' : BetaAt v' z' w')
    {last : ParallelStep F w' w}
    (row : StepProjection (singleContraction R)
      (.cons (singleContraction S') (.single (singleContraction T')))
      (.cons (singleContraction S) (.single (singleContraction T))) last)
    (inside : Internal (p ++ [.fn])
      (.cons (singleContraction S') (.single (singleContraction T'))))
    (V : BetaAt u a x)
    (predecessor : (singleContraction S).derivation.Residual ⟨a,V.redex⟩ ⟨z,T.redex⟩)
    (region : DisjointPositions s a ∨ ∃ q,a=(s++[.fn])++q) :
    ExtractionJoin
      (.of (.cons (singleContraction S') (.single (singleContraction T'))) (.cons S' (.single T')))
      (.of (.cons (singleContraction R) (.single (singleContraction V))) (.cons R (.single V))) := by
  obtain ⟨a',target,original,G,vertical,old,originalInside,projected⟩ :=
    function_residual_pullback R S T S' T' row inside V predecessor
  have originalR := projected.singleton_residual original V
  have firstR := row.head_singleton_residual S' S
  have firstInside : ∃ q,s'=(p++[.fn])++q := inside s' (by change s' ∈ [s',z']; simp)
  have oldInside := (Internal.single_iff original).mp originalInside
  let common := ExtractionRun.of (.single (singleContraction original)) (.single original)
  refine ⟨common,Extraction.single ?_,Extraction.single ?_⟩
  · rcases region with apart | function
    · have sourceApart := R.function_disjoint_reflect ⟨s',S'.redex⟩ ⟨a',original.redex⟩
        ⟨s,S.redex⟩ ⟨a,V.redex⟩ firstInside oldInside firstR originalR apart
      have image := S'.outside_residualSet_singleton ⟨a',original.redex⟩ sourceApart.1
      have selected := (singleContraction S').residual_image_target
        ⟨a',original.redex⟩ ⟨z',T'.redex⟩ image old
      obtain ⟨H,last',row'⟩ := singleton_projection_row S' original T' selected
      exact ExtractionStep.disjoint (.nil t) (.nil t) S' _ (.single original)
        _ (.single T') last' row' (by change 0 < 1; omega) a' sourceApart
        ((Internal.single_iff original).mpr ⟨[],(List.append_nil a').symm⟩)
    · have sourceInside := R.function_internal_reflect ⟨s',S'.redex⟩ ⟨a',original.redex⟩
        ⟨s,S.redex⟩ ⟨a,V.redex⟩ firstInside oldInside firstR originalR function
      obtain ⟨q,_,image⟩ := S'.function_residualSet_singleton ⟨a',original.redex⟩ sourceInside
      have selected := (singleContraction S').residual_image_target
        ⟨a',original.redex⟩ ⟨z',T'.redex⟩ image old
      obtain ⟨H,last',row'⟩ := singleton_projection_row S' original T' selected
      exact ExtractionStep.functionPart (.nil t) (.nil t) S' _ (.single original)
        _ (.single T') last' row' (by change 0 < 1; omega) ((Internal.single_iff original).mpr sourceInside)
  · exact ExtractionStep.functionPart (.nil t) (.nil t) R _ (.single original)
      _ (.single V) vertical projected (by change 0 < 1; omega) originalInside

end Lamping.Lambda
