import Lamping.Lambda.StandardFamilyChains
import Lamping.Lambda.ExtractionFamilyInvariance
namespace Lamping.Lambda

/-- Standard ordinary representatives of a genuine Copy zigzag have a common
actual extraction successor. Transitivity uses the proved extraction CR. -/
theorem StandardFamilyEq.common_extraction (chain : StandardFamilyEq a b)
    (source : RunRepresents r a) (target : RunRepresents s b) : ExtractionJoin r s := by
  induction chain generalizing r s with
  | copy relation _ _ sa sb => exact relation.standard_common_extraction source target sa sb
  | symm _ ih =>
    obtain ⟨z,left,right⟩ := ih target source
    exact ⟨z,right,left⟩
  | @trans a b c first last ih ik =>
    obtain ⟨w,S⟩ := b.redex.contract_exists
    have ordinary := first.properties.2.2.1
    let middle : ExtractionRun _ := .of (b.history.append (.single (singleContraction S)))
      (ordinary.append (.single S))
    have represented : RunRepresents middle b := ⟨S,ordinary,rfl⟩
    obtain ⟨x,rx,mx⟩ := ih source represented
    obtain ⟨y,my,sy⟩ := ik represented target
    obtain ⟨z,xz,yz⟩ := extraction_church_rosser _ mx my
    exact ⟨z,rx.trans xz,sy.trans yz⟩

/-- AG5.2.10--11 on actual ordinary representatives. Only the pointed prefixes
are required to be standard, including when the original family zigzag was not. -/
theorem FamilyEq.standard_common_extraction (family : FamilyEq a b)
    (source : RunRepresents r a) (target : RunRepresents s b)
    (sourceStandard : Standard a.history) (targetStandard : Standard b.history) : ExtractionJoin r s := by
  have ha : Atomic a.history := by obtain ⟨_,h,_⟩ := source; exact h
  have hb : Atomic b.history := by obtain ⟨_,h,_⟩ := target; exact h
  exact (family.standard_chain ha hb sourceStandard targetStandard).common_extraction source target

theorem family_iff_common_extraction (source : RunRepresents r a) (target : RunRepresents s b)
    (sourceStandard : Standard a.history) (targetStandard : Standard b.history) :
    FamilyEq a b ↔ ExtractionJoin r s := by
  constructor
  · intro family
    exact family.standard_common_extraction source target sourceStandard targetStandard
  · rintro ⟨z,left,right⟩
    exact common_extraction_family source target left right

end Lamping.Lambda
