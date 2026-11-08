import Lamping.Lambda.ExtractionFunctionRegionPeak
import Lamping.Lambda.ExtractionRegionGeometry
import Lamping.Lambda.ProjectionStepCongruence
import Lamping.Lambda.ProjectionSingletonSelection
namespace Lamping.Lambda

/-- One genuine inverse tile for the function/disjoint-or-function row
 pullback. Its back face keeps the supplied opposite contractions, and its
 new old-redex positions remain p and s'. -/
theorem function_region_pullback_tile
    (R : BetaAt t p u) (S : BetaAt u s v) (B : BetaAt v z w)
    (S' : BetaAt t s' v') (A : BetaAt v' a y) (R1 : BetaAt y p w)
    (row : StepProjection (singleContraction R)
      (.cons (singleContraction S') (.single (singleContraction A)))
      (.cons (singleContraction S) (.single (singleContraction B))) (singleContraction R1))
    (inside : Internal (p ++ [.fn])
      (.cons (singleContraction S') (.single (singleContraction A))))
    (V : BetaAt u q x) (S1 : BetaAt x s w)
    (lower : StepProjection (singleContraction S) (.single (singleContraction V))
      (.single (singleContraction B)) (singleContraction S1))
    (region : ExtractionRegion s (p ++ site)) (scope : ∃r,q=(p++site)++r) :
    ∃ (a' : Path) (target : Term) (original : BetaAt t a' target)
      (R0 : BetaAt target p x) (S0 : BetaAt target s' y),
      Internal ((p++[.fn,.body])++site) (.single (singleContraction original)) ∧
      ExtractionRegion s' ((p++[.fn,.body])++site) ∧
      StepProjection (singleContraction R) (.single (singleContraction original))
        (.single (singleContraction V)) (singleContraction R0) ∧
      StepProjection (singleContraction S') (.single (singleContraction original))
        (.single (singleContraction A)) (singleContraction S0) ∧
      StepProjection (singleContraction R0) (.single (singleContraction S0))
        (.single (singleContraction S1)) (singleContraction R1) := by
  have predecessor := lower.singleton_residual V B
  obtain ⟨a',target,original,G,vertical,old,originalInside,projected⟩ :=
    function_residual_pullback R S B S' A row inside V predecessor
  have originalR := projected.singleton_residual original V
  have firstR := row.head_singleton_residual S' S
  have firstInside : ∃q,s'=(p++[.fn])++q := inside s' (by change s'∈[s',a]; simp)
  have oldInside := (Internal.single_iff original).mp originalInside
  have oldScope := R.function_site_reflect ⟨a',original.redex⟩ ⟨q,V.redex⟩ oldInside originalR scope
  change ∃q,a'=((p++[.fn,.body])++site)++q at oldScope
  obtain ⟨qs,sourceS,targetS⟩ := R.function_residual_coordinates ⟨s',S'.redex⟩ ⟨s,S.redex⟩ firstInside firstR
  change s'=(p++[.fn,.body])++qs at sourceS
  change s=p++qs at targetS
  have localRegion : ExtractionRegion qs site := by
    apply (ExtractionRegion.prefix_iff p qs site).mp
    simpa only [targetS] using region
  have originalRegion : ExtractionRegion s' ((p++[.fn,.body])++site) := by
    rw [sourceS]
    exact (ExtractionRegion.prefix_iff (p++[.fn,.body]) qs site).mpr localRegion
  have image : (singleContraction S').residualSet [a'] = [a] := by
    rcases originalRegion with apart | function
    · exact (singleContraction S').residual_image_target ⟨a',original.redex⟩ ⟨a,A.redex⟩
        (S'.outside_residualSet_singleton ⟨a',original.redex⟩ (apart.descendant_outside oldScope)) old
    · have originalFunction : ∃r,a'=(s'++[.fn])++r := by simpa only [function] using oldScope
      obtain ⟨r,_,selection⟩ := S'.function_residualSet_singleton ⟨a',original.redex⟩ originalFunction
      exact (singleContraction S').residual_image_target ⟨a',original.redex⟩ ⟨a,A.redex⟩ selection old
  obtain ⟨H,lastS,projectedS⟩ := singleton_projection_row S' original A image
  have functionRegion : ExtractionRegion p (p++[.fn]) := .inr rfl
  have outsideR : ¬∃r,p=(p++[.fn])++r := functionRegion.root_outside
  have selectedR := projected.final_selection_singleton rfl ⟨p,R.redex⟩ rfl (.single original) originalInside outsideR
  obtain ⟨pathsR,R0⟩ := projected.final_vertical_singleton originalInside outsideR
  have rowR := projected.last_congr selectedR pathsR (last' := singleContraction R0)
  have originalScoped := (Internal.single_iff original).mpr oldScope
  have selectedS := projectedS.final_selection_singleton rfl ⟨s',S'.redex⟩ rfl (.single original)
    originalScoped originalRegion.root_outside
  obtain ⟨pathsS,S0⟩ := projectedS.final_vertical_singleton originalScoped originalRegion.root_outside
  have rowS := projectedS.last_congr selectedS pathsS (last' := singleContraction S0)
  obtain ⟨qs',sourceS0,imageS0⟩ := R0.function_residualSet_singleton ⟨s',S0.redex⟩ firstInside
  have qsEq : qs'=qs := List.append_cancel_left (sourceS0.symm.trans sourceS)
  have backR : (singleContraction R0).residualSet [s'] = [s] := by
    rw [imageS0,qsEq,←targetS]
  have backS : (singleContraction S0).residualSet [p] = [p] :=
    S0.outside_residualSet_singleton ⟨p,R0.redex⟩ (functionRegion.not_above firstInside)
  let square : ParallelMovesSquare [p] [s'] target x y w :=
    ⟨singleContraction R0,singleContraction S0,
      backR.symm ▸ singleContraction S1,backS.symm ▸ singleContraction R1⟩
  have built := StepProjection.cons square (.nil square.afterSecond)
  have normalized := built.last_congr backS (ParallelStep.paths_cast backS.symm (singleContraction R1))
    (last' := singleContraction R1)
  have front : StepProjection (singleContraction R0) (.single (singleContraction S0))
      (.single (singleContraction S1)) (singleContraction R1) := by
    simpa only [square,ParallelHistory.single,ParallelHistory.cons_selection_cast] using normalized
  exact ⟨a',target,original,R0,S0,originalScoped,originalRegion,rowR,rowS,front⟩

end Lamping.Lambda
