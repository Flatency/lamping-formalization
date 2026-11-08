import Lamping.Lambda.FunctionRegionPullback
namespace Lamping.Lambda

/-- A nonempty later region in a function-row overlap is wholly below the
 retained outer occurrence. This is derived from its first actual tile. -/
theorem function_region_site
    (R : BetaAt t p u) (S' : BetaAt t s' v) (S : BetaAt u s w) (R' : BetaAt v p w)
    (front : StepProjection (singleContraction R) (.single (singleContraction S'))
      (.single (singleContraction S)) (singleContraction R'))
    (firstInside : ∃q,s'=(p++[.fn])++q)
    (upper : ParallelHistory v upperEnd) (hu : Atomic upper)
    (middle : ParallelHistory w jointEnd) (hm : Atomic middle)
    (lower : ParallelHistory u lowerEnd) (hl : Atomic lower)
    {lastR : ParallelStep F upperEnd jointEnd} {lastS : ParallelStep G lowerEnd jointEnd}
    (upperRow : StepProjection (singleContraction R') upper middle lastR)
    (lowerRow : StepProjection (singleContraction S) lower middle lastS)
    (upperInside : Internal (p++[.fn]) upper)
    (positive : 0 < lower.length)
    (region : ExtractionRegion s site) (lowerInside : Internal site lower) :
    ∃q,site=p++q := by
  cases hl with
  | nil => simp only [ParallelHistory.length] at positive; omega
  | @cons u q x lowerEnd lowerRest V hlrest =>
    cases hm with
    | nil => have len := lowerRow.length; simp only [ParallelHistory.length] at len; omega
    | @cons w z joint jointEnd middleRest B hmrest =>
      cases hu with
      | nil => have len := upperRow.length; simp only [ParallelHistory.length] at len; omega
      | @cons v a y upperEnd upperRest A hurest =>
        have aInside : ∃r,a=(p++[.fn])++r := upperInside a
          (by change a∈a::upperRest.derivation.paths; exact List.mem_cons_self)
        have vScope : ∃r,q=site++r := lowerInside q
          (by change q∈q::lowerRest.derivation.paths; exact List.mem_cons_self)
        obtain ⟨R1,headUpper,_⟩ := upperRow.region_head R' A B (.inr rfl) aInside
        have core := front.append headUpper
        have coreInside : Internal (p++[.fn])
            (.cons (singleContraction S') (.single (singleContraction A))) := by
          intro name hq
          change name∈[s',a] at hq
          rcases List.mem_cons.mp hq with he | he
          · cases he; exact firstInside
          · cases List.mem_singleton.mp he; exact aInside
        have old := lowerRow.head_singleton_residual V B
        obtain ⟨a',target,V',K,vertical,_,vInside,projected⟩ :=
          function_residual_pullback R S B S' A core coreInside V old
        have firstOld := front.singleton_residual S' S
        obtain ⟨qs,_,sInside⟩ := R.function_residual_coordinates
          ⟨s',S'.redex⟩ ⟨s,S.redex⟩ firstInside firstOld
        have vOld := projected.singleton_residual V' V
        obtain ⟨qv,_,vTarget⟩ := R.function_residual_coordinates
          ⟨a',V'.redex⟩ ⟨q,V.redex⟩ ((Internal.single_iff V').mp vInside) vOld
        exact region.site_inside ⟨qs,sInside⟩ ⟨qv,vTarget⟩ vScope

end Lamping.Lambda
