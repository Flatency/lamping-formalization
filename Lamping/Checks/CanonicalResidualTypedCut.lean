import Lamping.Lamping.CanonicalResidualTypedCut
import Lamping.Checks.CancellationFrontGeometry
namespace Lamping.Checks.CanonicalResidualTypedCut
open AG Graph
private abbrev site := CancellationPrefixFixture.geometrySite
private abbrev principal := CancellationPrefixFixture.geometryPrincipal
private abbrev cut := cutFragment site.net (pathPartition (.fanCancel 1) Empty) site.closed
private abbrev rhs := (Schema.fanCancel 1).right.net

/-- The actual kept-lambda fan fixture supplies the untyped-front hypothesis
internally. The old split is literal, including the parent terminal. -/
theorem actual_typed_cut
    (relation : CanonicalWireResidual cut rhs site.net site.outsideEnd
      (site.cancellation_canonical_fronts principal.edges) raw old)
    (split : old=pre++post) (typed : ∃ k,accessKind site.net pre=some k)
    (nonempty : post≠[]) :
    ∃ rawPre rawPost,raw=rawPre++rawPost ∧
      CanonicalWireResidual cut rhs site.net site.outsideEnd
        (site.cancellation_canonical_fronts principal.edges) rawPre pre ∧
      CanonicalWireResidual cut rhs site.net site.outsideEnd
        (site.cancellation_canonical_fronts principal.edges) rawPost post :=
  CanonicalWireResidual.split_at_typed_prefix cut rhs site.net site.outsideEnd
    (site.cancellation_canonical_fronts principal.edges)
    CancellationFrontGeometry.actual_all_fronts_untyped relation split typed nonempty

#print axioms CanonicalWireResidual.split_at_typed_prefix
#print axioms actual_typed_cut
end Lamping.Checks.CanonicalResidualTypedCut
