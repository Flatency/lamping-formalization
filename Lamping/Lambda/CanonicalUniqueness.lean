import Lamping.Lambda.FamilyCommonExtraction
import Lamping.Lambda.CanonicalExistence
namespace Lamping.Lambda

theorem RunRepresents.prefix_standard_of_standard (represented : RunRepresents r a)
    (standard : Standard r.history) : Standard a.history := by
  obtain ⟨last,_,history⟩ := represented
  rw [history] at standard
  exact standard.prefix

theorem ExtractionNormal.eq_of_extraction (normal : ExtractionNormal r)
    (steps : Extraction r s) : r=s := by
  cases steps with
  | refl => rfl
  | cons step _ => exact False.elim (normal ⟨_,step⟩)

/-- Two canonical ordinary representatives of the same family coincide as
actual runs. The proof uses common extraction and normality, not endpoints. -/
theorem canonical_family_unique (left : CanonicalRun r) (right : CanonicalRun s)
    (source : RunRepresents r a) (target : RunRepresents s b) (family : FamilyEq a b) : r=s := by
  obtain ⟨z,rz,sz⟩ := family.standard_common_extraction source target
    (source.prefix_standard_of_standard left.2.1) (target.prefix_standard_of_standard right.2.1)
  exact (left.2.2.eq_of_extraction rz).trans (right.2.2.eq_of_extraction sz).symm

/-- A standard pointed ordinary representative extracts to any given canonical
representative of its family. Its full run need not be standard. -/
theorem FamilyEq.extract_canonical (family : FamilyEq a b)
    (source : RunRepresents r a) (target : RunRepresents c b)
    (sourceStandard : Standard a.history) (canonical : CanonicalRun c) : Extraction r c := by
  obtain ⟨z,rz,cz⟩ := family.standard_common_extraction source target sourceStandard
    (target.prefix_standard_of_standard canonical.2.1)
  have eq := canonical.2.2.eq_of_extraction cz
  cases eq
  exact rz

/-- Existence and uniqueness in every arbitrary pointed family. This is an
existential theorem, with no claim of an effective canonicalization algorithm. -/
theorem RedexWithHistory.canonical_exists_unique (a : RedexWithHistory m) :
    ∃ (r : ExtractionRun m) (b : RedexWithHistory m),
      CanonicalRun r ∧ RunRepresents r b ∧ FamilyEq a b ∧
      ∀ (s : ExtractionRun m) (c : RedexWithHistory m),
        CanonicalRun s → RunRepresents s c → FamilyEq a c → s=r := by
  obtain ⟨r,b,canonical,represented,family⟩ := a.canonical_exists
  refine ⟨r,b,canonical,represented,family,?_⟩
  intro s c other otherRep otherFamily
  exact canonical_family_unique other canonical otherRep represented (.trans (.symm otherFamily) family)

end Lamping.Lambda
