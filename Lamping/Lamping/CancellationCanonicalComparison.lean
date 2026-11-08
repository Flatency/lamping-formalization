import Lamping.Lamping.CancellationFrontGeometry
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

private theorem outside_injective : Function.Injective site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition s V)
  have mapped := congrArg split same
  change split (split.invFun (.inl e))=split (split.invFun (.inl f)) at mapped
  simp only [split.right_inv] at mapped
  exact Sum.inl.inj mapped

/-- Actual fixed cancellation routes fill the delimiter and frontier
conditions; target uniqueness is not assumed on the relation. -/
theorem CanonicalCancellationResidual.target_unique (cancel : IsCancellation s)
    (principal : SiteActionPrincipal site) {first second old}
    (left : CanonicalCancellationResidual site (site.cancellation_canonical_fronts principal.edges) first old)
    (right : CanonicalCancellationResidual site (site.cancellation_canonical_fronts principal.edges) second old) :
    first=second := by
  let c := cutFragment site.net (pathPartition s V) site.closed
  let r := s.right.net
  cases cancel
  all_goals
    have raw := CanonicalWireResidual.target_unique c r site.net site.outsideEnd
      (site.cancellation_canonical_fronts principal.edges) (outside_injective site)
      (fun frontier=>by
        obtain ⟨inside,tail,literal,disjoint⟩ := cancellation_front_internal_delimiter site principal frontier
        exact ⟨c.wire (.inr (.inl (.inr frontier))),inside,tail,literal,disjoint⟩)
      (fun f h same=>cancellation_front_heads_injective site principal same) left right rfl
    change first.map (plugEnd c.label r.label).invFun=second.map (plugEnd c.label r.label).invFun at raw
    have actual := congrArg (List.map (plugEnd c.label r.label)) raw
    simpa only [List.map_map,Function.comp_def,(plugEnd c.label r.label).right_inv,List.map_id_fun'] using actual

/-- On the actual canonical residual witnesses, equality is reflected and
preserved. Identifying these witnesses with syntax fragments is separate. -/
theorem CanonicalCancellationResidual.equality_iff (cancel : IsCancellation s)
    (principal : SiteActionPrincipal site) {first second oldFirst oldSecond}
    (left : CanonicalCancellationResidual site (site.cancellation_canonical_fronts principal.edges) first oldFirst)
    (right : CanonicalCancellationResidual site (site.cancellation_canonical_fronts principal.edges) second oldSecond) :
    first=second ↔oldFirst=oldSecond := by
  constructor
  · intro equal
    subst second
    exact CanonicalCancellationResidual.source_unique site cancel left right
  · intro equal
    subst oldSecond
    exact CanonicalCancellationResidual.target_unique site cancel principal left right
end
end Lamping.AG