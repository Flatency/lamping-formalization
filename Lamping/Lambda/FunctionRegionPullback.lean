import Lamping.Lambda.FunctionRegionPullbackTile
import Lamping.Lambda.RegionProjectionHead
import Lamping.Lambda.ProjectionSplits
namespace Lamping.Lambda

/-- Ordinary inverse-row pullback for LEV80 (3,2)/(3,3). Both supplied rows
 end in the same actual middle schedule. Every missing original contraction
 and every back tile are constructed, retaining the fixed source region. -/
theorem function_region_pullback
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
    (region : ExtractionRegion s (p++site)) (lowerInside : Internal (p++site) lower) :
    ∃ (target : Term) (original : ParallelHistory t target) (_ho : Atomic original)
      (finalR : BetaAt target p lowerEnd) (finalS : BetaAt target s' upperEnd),
      Internal ((p++[.fn,.body])++site) original ∧
      ExtractionRegion s' ((p++[.fn,.body])++site) ∧
      StepProjection (singleContraction R) original lower (singleContraction finalR) ∧
      StepProjection (singleContraction S') original upper (singleContraction finalS) := by
  have firstOld := front.singleton_residual S' S
  obtain ⟨qs,sourceS,targetS⟩ := R.function_residual_coordinates ⟨s',S'.redex⟩ ⟨s,S.redex⟩ firstInside firstOld
  change s'=(p++[.fn,.body])++qs at sourceS
  change s=p++qs at targetS
  have localRegion : ExtractionRegion qs site := (ExtractionRegion.prefix_iff p qs site).mp (targetS ▸ region)
  have originalRegion : ExtractionRegion s' ((p++[.fn,.body])++site) := by
    rw [sourceS]
    exact (ExtractionRegion.prefix_iff (p++[.fn,.body]) qs site).mpr localRegion
  induction hl generalizing t v w with
  | nil =>
    cases hm with
    | cons B ht => have len := lowerRow.length; simp only [ParallelHistory.length] at len; omega
    | nil =>
      cases hu with
      | cons A ht => have len := upperRow.length; simp only [ParallelHistory.length] at len; omega
      | nil =>
        have empty : Internal ((p++[.fn,.body])++site) (ParallelHistory.nil t) := by
          intro q hq
          cases hq
        exact ⟨t,.nil t,.nil t,R,S',empty,originalRegion,.nil _,.nil _⟩
  | @cons u q x lowerEnd lowerRest V hlrest ih =>
    cases hm with
    | nil => have len := lowerRow.length; simp only [ParallelHistory.length] at len; omega
    | @cons w z joint jointEnd middleRest B hmrest =>
      cases hu with
      | nil => have len := upperRow.length; simp only [ParallelHistory.length] at len; omega
      | @cons v a y upperEnd upperRest A hurest =>
        have aInside : ∃r,a=(p++[.fn])++r := upperInside a
          (by change a∈a::upperRest.derivation.paths; exact List.mem_cons_self)
        have vScope : ∃r,q=(p++site)++r := lowerInside q
          (by change q∈q::lowerRest.derivation.paths; exact List.mem_cons_self)
        obtain ⟨R1,headUpper,tailUpper⟩ := upperRow.region_head R' A B (.inr rfl) aInside
        obtain ⟨S1,headLower,tailLower⟩ := lowerRow.region_head S V B region vScope
        have core := front.append headUpper
        have coreInside : Internal (p++[.fn])
            (.cons (singleContraction S') (.single (singleContraction A))) := by
          intro q hq
          change q∈[s',a] at hq
          rcases List.mem_cons.mp hq with he | he
          · cases he; exact firstInside
          · cases List.mem_singleton.mp he; exact aInside
        obtain ⟨a',target,V',R0,S0,scopeV',region',rowR,rowS,newFront⟩ :=
          function_region_pullback_tile R S B S' A R1 core coreInside V S1 headLower region vScope
        have upperRestInside : Internal (p++[.fn]) upperRest := by
          intro q hq
          exact upperInside q (by change q∈a::upperRest.derivation.paths; exact List.mem_cons_of_mem _ hq)
        have lowerRestInside : Internal (p++site) lowerRest := by
          intro name hq
          exact lowerInside name (by change name∈q::lowerRest.derivation.paths; exact List.mem_cons_of_mem _ hq)
        obtain ⟨lastTarget,rest,hr,finalR,finalS,restInside,_,lastRowR,lastRowS⟩ :=
          ih R0 S0 S1 R1 newFront upperRest hurest middleRest hmrest
            tailUpper tailLower upperRestInside lowerRestInside
            (newFront.singleton_residual S0 S1)
        refine ⟨lastTarget,.cons (singleContraction V') rest,.cons V' hr,finalR,finalS,?_,
          originalRegion,rowR.append lastRowR,rowS.append lastRowS⟩
        intro q hq
        change q∈a'::rest.derivation.paths at hq
        rcases List.mem_cons.mp hq with he | he
        · cases he; exact (Internal.single_iff V').mp scopeV'
        · exact restInside q he

end Lamping.Lambda
