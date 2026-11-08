import Lamping.Lamping.CanonicalResidualTypedCut
import Lamping.Lamping.CancellationFrontGeometry
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- A typed cut in the old path induces an exact cut in the actual reduced
path. The principal is the same supplied witness in both sub-residuals. -/
theorem CanonicalCancellationResidual.split_at_typed_prefix
    (cancel : IsCancellation s) (principal : SiteActionPrincipal site)
    (relation : CanonicalCancellationResidual site
      (site.cancellation_canonical_fronts principal.edges) es old)
    (split : old=pre++post) (typed : ∃ k,accessKind site.net pre=some k)
    (nonempty : post≠[]) :
    ∃ esPre esPost,es=esPre++esPost ∧
      CanonicalCancellationResidual site (site.cancellation_canonical_fronts principal.edges) esPre pre ∧
      CanonicalCancellationResidual site (site.cancellation_canonical_fronts principal.edges) esPost post := by
  let c := cutFragment site.net (pathPartition s V) site.closed
  let r := s.right.net
  cases cancel
  all_goals
    obtain ⟨rawPre,rawPost,rawSplit,first,second⟩ :=
      CanonicalWireResidual.split_at_typed_prefix c r site.net site.outsideEnd
        (site.cancellation_canonical_fronts principal.edges)
        (cancellation_front_segments_untyped site (by constructor) principal) relation split typed nonempty
    refine ⟨rawPre.map (plugEnd c.label r.label),rawPost.map (plugEnd c.label r.label),?_,?_,?_⟩
    · change es.map (plugEnd c.label r.label).invFun=rawPre++rawPost at rawSplit
      have mapped := congrArg (List.map (plugEnd c.label r.label)) rawSplit
      simpa only [List.map_append,List.map_map,Function.comp_def,
        (plugEnd c.label r.label).right_inv,List.map_id_fun'] using mapped
    · change CanonicalWireResidual c r site.net site.outsideEnd
        (site.cancellation_canonical_fronts principal.edges)
        ((rawPre.map (plugEnd c.label r.label)).map (plugEnd c.label r.label).invFun) pre
      simpa only [List.map_map,Function.comp_def,
        (plugEnd c.label r.label).left_inv,List.map_id_fun'] using first
    · change CanonicalWireResidual c r site.net site.outsideEnd
        (site.cancellation_canonical_fronts principal.edges)
        ((rawPost.map (plugEnd c.label r.label)).map (plugEnd c.label r.label).invFun) post
      simpa only [List.map_map,Function.comp_def,
        (plugEnd c.label r.label).left_inv,List.map_id_fun'] using second
end
end Lamping.AG
