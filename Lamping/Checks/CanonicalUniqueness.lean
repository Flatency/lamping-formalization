import Lamping.Lambda.CanonicalUniqueness
import Lamping.Checks.CopyCommonExtraction
import Lamping.Checks.CanonicalExistence
namespace Lamping.Checks.CanonicalUniqueness
open Lambda

example (source : RunRepresents r a) (target : RunRepresents s b)
    (ha : Standard a.history) (hb : Standard b.history) :
    FamilyEq a b ↔ ExtractionJoin r s := family_iff_common_extraction source target ha hb

/-- The original non-atomic empty parallel step is still allowed, without
asserting direct extraction from that non-ordinary history. -/
example : ∃ (r : ExtractionRun CanonicalExistence.omegaTerm)
    (b : RedexWithHistory CanonicalExistence.omegaTerm),
    CanonicalRun r ∧ RunRepresents r b ∧ FamilyEq CanonicalExistence.pointedEmpty b ∧
    ∀ (s : ExtractionRun CanonicalExistence.omegaTerm) (c : RedexWithHistory CanonicalExistence.omegaTerm),
      CanonicalRun s → RunRepresents s c → FamilyEq CanonicalExistence.pointedEmpty c → s=r :=
  CanonicalExistence.pointedEmpty.canonical_exists_unique

/-- A genuinely nonstandard full run extracts to the canonical member of its
family: only its actual pointed prefix is standard. -/
example : ∃ c, CanonicalRun c ∧ Extraction CopyCommonExtraction.nonstandardFull c ∧
    ¬Standard CopyCommonExtraction.nonstandardFull.history := by
  open CopyCommonExtraction in
    let a : RedexWithHistory twins := ⟨twins,.single (singleContraction rightBeta),⟨[.fn],leftBeta.redex⟩⟩
    have represented : RunRepresents nonstandardFull a := ⟨leftBeta,.single rightBeta,rfl⟩
    have standard : Standard a.history := Standard.single_step _ ⟨[.arg],rightBeta.redex⟩ (leftmost_singleton _)
    obtain ⟨c,b,canonical,target,family⟩ := a.canonical_exists
    exact ⟨c,canonical,family.extract_canonical represented target standard canonical,nonstandardFull_not_standard⟩

example (left : CanonicalRun r) (right : CanonicalRun s)
    (source : RunRepresents r a) (target : RunRepresents s b) (family : FamilyEq a b) : a=b := by
  have eq := canonical_family_unique left right source target family
  cases eq
  exact source.unique target

#print axioms FamilyEq.standardize
#print axioms StandardFamilyEq.common_extraction
#print axioms family_iff_common_extraction
#print axioms canonical_family_unique
#print axioms FamilyEq.extract_canonical
#print axioms RedexWithHistory.canonical_exists_unique
end Lamping.Checks.CanonicalUniqueness
