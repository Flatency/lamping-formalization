import Lamping.Lambda.ExtractionFamilyEvents
import Lamping.Lambda.FamilyStandardization
import Lamping.Lambda.CanonicalCopyAncestor
import Lamping.Lambda.FamilyDevelopmentJoin
namespace Lamping.Lambda

/-- Every family event before a canonical representative's final redex was
already used in the proper prefix of any pointed member of that family. -/
theorem canonical_prefix_relative {canonicalRun : ExtractionRun m}
    {a b : RedexWithHistory m} (canonical : CanonicalRun canonicalRun)
    (represented : RunRepresents canonicalRun a) (family : FamilyEq a b) :
    RelativeFamilies a.history (FamilyUsed b.history) := by
  obtain ⟨ordinary,atomic,standard,perm,support⟩ :=
    atomic_standardization_exists_relative b.history
  let point : RedexWithHistory m := ⟨b.target,ordinary,b.redex⟩
  have changed : FamilyEq point a :=
    .trans (.symm (FamilyEq.of_permutation b ordinary perm)) family.symm
  obtain ⟨endB,lastB⟩ := b.redex.contract_exists
  let run : ExtractionRun m := .of (ordinary.append (.single (singleContraction lastB)))
    (atomic.append (.single lastB))
  have pointRep : RunRepresents run point := ⟨lastB,atomic,rfl⟩
  have extracts := changed.extract_canonical pointRep represented standard canonical
  exact fun event used => support event (extracts.pointed_family_events pointRep represented event used)

/-- An exhausted development covers the canonical prefix of every family
whose canonical prefix uses only that development's families. -/
theorem canonical_copy_of_development {canonicalRun : ExtractionRun m}
    {a b : RedexWithHistory m} (canonical : CanonicalRun canonicalRun)
    (represented : RunRepresents canonicalRun a) (family : FamilyEq a b)
    (relative : RelativeFamilies a.history X) (development : DevelopsFamilies b.history X) :
    Copy a b :=
  (canonical_copy_iff_history_prefix canonical represented family).mpr
    (relative.prefix_development development)

end Lamping.Lambda
