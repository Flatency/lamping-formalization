import Lamping.Lamping.CancellationResidualTypedCut
import Lamping.Checks.CancellationFrontGeometry
namespace Lamping.Checks.CancellationResidualTypedCut
open AG Graph
private abbrev site := CancellationPrefixFixture.geometrySite
private abbrev principal := CancellationPrefixFixture.geometryPrincipal

/-- A supplied actual residual is cut in the reduced graph, without a raw
plug-segment oracle or any frontier side conditions from the caller. -/
theorem actual_reduced_typed_cut
    (relation : CanonicalCancellationResidual site
      (site.cancellation_canonical_fronts principal.edges) es old)
    (split : old=pre++post) (typed : ∃ k,accessKind site.net pre=some k)
    (nonempty : post≠[]) :
    ∃ esPre esPost,es=esPre++esPost ∧
      CanonicalCancellationResidual site (site.cancellation_canonical_fronts principal.edges) esPre pre ∧
      CanonicalCancellationResidual site (site.cancellation_canonical_fronts principal.edges) esPost post :=
  CanonicalCancellationResidual.split_at_typed_prefix site (.fan 1) principal
    relation split typed nonempty

#print axioms CanonicalCancellationResidual.split_at_typed_prefix
#print axioms actual_reduced_typed_cut
end Lamping.Checks.CancellationResidualTypedCut
