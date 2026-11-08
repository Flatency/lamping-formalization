import Lamping.Lamping.BetaFixedSourcePrefixes
namespace Lamping.AG
open Graph
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
private theorem port_endpoint_eq {n m : K⊕(Unit⊕Unit)}
    {p : Port (site.net.label n).sort} {q : Port (site.net.label m).sort}
    (same : n=m) (role : HEq p q) :
    (.inl ⟨n,p⟩ : Endpoint site.net)=.inl ⟨m,q⟩ := by
  subst m
  cases eq_of_heq role
  rfl
/-- The fixed actual beta principal is the same finite internal transparent
component used by the generic site geometry. The name of the presentation
carries no action-schema assumption. -/
def SiteBetaGeometry.principal_presentation {edge : BetaEdge site.net}
    (geometry : SiteBetaGeometry site edge) : SiteActionPrincipal site where
  edges := edge.principal
  first := by
    have nodes : edge.app=.inr (.inl ()) := congrArg Sigma.fst (Sum.inl.inj geometry.appCtx)
    have ports := port_endpoint_eq site nodes edge.appFun_role
    exact edge.principalStart.trans (congrArg some ports)
  last := by
    have nodes : edge.lam=.inr (.inr ()) := congrArg Sigma.fst (Sum.inl.inj geometry.body)
    have ports := port_endpoint_eq site nodes edge.lamCtx_role
    exact edge.principalEnd.trans (congrArg (fun e => some (site.net.wire e)) ports)
  transparent := edge.transparent

theorem SiteBetaGeometry.principal_internal {edge : BetaEdge site.net}
    (geometry : SiteBetaGeometry site edge) :
    ∀ e∈edge.principal,∃ internal,e=site.internalEnd internal :=
  (geometry.principal_presentation site).internal_segments site

theorem SiteBetaGeometry.reverse_internal {edge : BetaEdge site.net}
    (geometry : SiteBetaGeometry site edge) :
    ∀ e∈edge.reverseRoute,∃ internal,e=site.internalEnd internal :=
  (geometry.principal_presentation site).reverse_internal_segments site
end
end Lamping.AG