import Lamping.Lambda.StandardizationGeneral
import Lamping.Lambda.ExtractionStandardness
import Lamping.Lambda.ExtractionFamilyInvariance
namespace Lamping.Lambda
/-- Every arbitrary pointed parallel history has a same-family canonical
ordinary representative. Extraction starts after genuine atomic
standardization; the original history need not be atomic or standard. -/
theorem RedexWithHistory.canonical_exists (a : RedexWithHistory m) :
    ∃ (r : ExtractionRun m) (b : RedexWithHistory m), CanonicalRun r ∧ RunRepresents r b ∧ FamilyEq a b := by
  obtain ⟨σ,atomic,standard,perm⟩ := atomic_standardization_exists a.history
  let standardized : RedexWithHistory m := ⟨a.target,σ,a.redex⟩
  have sameFamily : FamilyEq a standardized := FamilyEq.of_permutation a σ perm
  obtain ⟨target,last⟩ := a.redex.contract_exists
  let initial : ExtractionRun m := .of (σ.append (.single (singleContraction last))) (atomic.append (.single last))
  have represented : RunRepresents initial standardized := ⟨last,atomic,rfl⟩
  have prefixStandard : PrefixStandard initial := ⟨standardized,represented,standard⟩
  obtain ⟨canonical,steps,canonicalProof⟩ := canonical_extraction_exists prefixStandard
  obtain ⟨point,representsPoint⟩ := canonical.represents_exists canonicalProof.1
  exact ⟨canonical,point,canonicalProof,representsPoint,
    .trans sameFamily (steps.family standardized point represented representsPoint)⟩
end Lamping.Lambda
