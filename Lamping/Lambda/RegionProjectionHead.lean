import Lamping.Lambda.ExtractionRegionGeometry
import Lamping.Lambda.ProjectionStepCongruence
import Lamping.Lambda.ProjectionSingletonSelection
import Lamping.Lambda.ExtractionInternal
namespace Lamping.Lambda

/-- Normalize an actual head tile in either source extraction region while
 preserving the entire given tail row and the head's prescribed beta. -/
theorem StepProjection.region_head (R : BetaAt t p u) (A : BetaAt t a v) (B : BetaAt u b w)
    (row : StepProjection (singleContraction R) (.cons (singleContraction A) σ)
      (.cons (singleContraction B) τ) last)
    (region : ExtractionRegion p site) (inside : ∃q,a=site++q) :
    ∃ R1 : BetaAt v p w,
      StepProjection (singleContraction R) (.single (singleContraction A))
        (.single (singleContraction B)) (singleContraction R1) ∧
      StepProjection (singleContraction R1) σ τ last := by
  have old := row.head_singleton_residual A B
  have sideSelection := R.region_residual_image ⟨a,A.redex⟩ ⟨b,B.redex⟩ region inside old
  obtain ⟨sq,hfirst,htop,_,hside,remaining⟩ := row.head_square
  cases sq with
  | mk first top side vertical =>
    cases hfirst
    cases htop
    have paths : side.paths = [b] := congrArg Derivation.paths hside
    have sideEq := ParallelHistory.single_eq_of_selection_paths B sideSelection paths (h := side)
    have head : StepProjection (singleContraction R) (.single (singleContraction A))
        (.single (singleContraction B)) vertical := by
      rw [←sideEq]
      exact .cons ⟨singleContraction R,singleContraction A,side,vertical⟩ (.nil vertical)
    have hi := (Internal.single_iff A).mpr inside
    have selected := head.final_selection_singleton rfl ⟨p,R.redex⟩ rfl (.single A) hi region.root_outside
    obtain ⟨verticalPaths,R1⟩ := head.final_vertical_singleton hi region.root_outside
    exact ⟨R1,head.last_congr selected verticalPaths,
      remaining.first_congr selected verticalPaths⟩

end Lamping.Lambda
