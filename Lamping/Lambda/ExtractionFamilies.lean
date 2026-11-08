import Lamping.Lambda.ExtractionClosure
import Lamping.Lambda.FiniteSelections
namespace Lamping.Lambda
 theorem extraction_rank_one_normal (r : ExtractionRun m) (he : r.rank = 1) : ExtractionNormal r := by
   rintro ⟨s, hs⟩
   have hlt := hs.rank_lt
   have hp := hs.positive
   omega

/-- The first extraction rule preserves the pointed family's true history.
 This proof does not use labels, endpoint identity or an extraction invariant
 packaged as a premise. -/
 theorem residual_extraction_family (ρ : ParallelHistory m t)
     (R : BetaAt t p u) (S : BetaAt u q v) (S' : BetaAt t q' v')
     (hs : (singleContraction R).derivation.Residual ⟨q', S'.redex⟩ ⟨q, S.redex⟩) :
     FamilyEq ⟨u, ρ.append (.single (singleContraction R)), ⟨q, S.redex⟩⟩
       ⟨t, ρ, ⟨q', S'.redex⟩⟩ := by
   apply FamilyEq.symm
   exact .copy ⟨.single (singleContraction R), .refl _, by
     simpa only [ParallelHistory.single_derivation] using hs⟩
end Lamping.Lambda
