import Lamping.Lamping.SourceRouteEvaluation
import Lamping.Lamping.PathSiteBetaLifting
import Lamping.Lamping.BetaChainEvaluatedResiduals
import Lamping.Lamping.InteriorSourceBlockEndpoints

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem role_endpoint_eq
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {T : Type} {canonical : T} {n m : N}
    {p : Port (g.label n).sort} {q : Port (g.label m).sort}
    (nodes : n=m) (left : HEq p canonical) (right : HEq q canonical) :
    (.inl ⟨n,p⟩ : Endpoint g)=.inl ⟨m,q⟩ := by
  subst m
  cases eq_of_heq (left.trans right.symm)
  rfl

/-- Transfer exactly six endpoint roles; no principal route equality. -/
theorem BetaSourcePorts.rebase_nodes
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {original : LTerm} {root : B}
    {first second : BetaEdge g} {appId lamId : Labelled.Label}
    (ports : BetaSourcePorts original root first appId lamId)
    (sameApp : first.app=second.app) (sameLam : first.lam=second.lam) :
    BetaSourcePorts original root second appId lamId := by
  have appContextEnd := role_endpoint_eq sameApp first.appCtx_role second.appCtx_role
  have functionEnd : first.funEnd=second.funEnd :=
    role_endpoint_eq sameApp first.appFun_role second.appFun_role
  have argumentEnd : first.argEnd=second.argEnd :=
    role_endpoint_eq sameApp first.appArg_role second.appArg_role
  have contextEnd : first.ctxEnd=second.ctxEnd :=
    role_endpoint_eq sameLam first.lamCtx_role second.lamCtx_role
  have bodyEnd := role_endpoint_eq sameLam first.lamBody_role second.lamBody_role
  have bindingEnd := role_endpoint_eq sameLam first.lamBind_role second.lamBind_role
  exact ⟨appContextEnd ▸ ports.appContext,functionEnd ▸ ports.appFunction,
    argumentEnd ▸ ports.appArgument,contextEnd ▸ ports.lamContext,
    bodyEnd ▸ ports.lamBody,bindingEnd ▸ ports.lamBinding⟩

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- The supplied producer edge and selector stay fixed throughout the walk. -/
theorem PathSite.fixed_producer_route_walk
    {root : B} {original : LTerm} (initial : INIT original)
    (matching : Matches site.net root original.erase)
    {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    (selection : SourceEdgeSelection original site.net root)
    {start finish : SourcePort} {stamp : Labelled.Label}
    (route : SelectedSourceRoute (sourceEdges [] .external original)
      (SelectedDegree original (site.betaSyntaxFiber root original.erase)) start stamp finish) :
    ∃walk : PhysicalSourceWalk original root edge start stamp finish,
      walk.edges=selection.evalLabel edge stamp := by
  have actualApp : edge.app=.inr (.inl ()) :=
    congrArg Sigma.fst (Sum.inl.inj geometry.appCtx)
  have actualLam : edge.lam=.inr (.inr ()) :=
    congrArg Sigma.fst (Sum.inl.inj geometry.body)
  obtain ⟨other,otherApp,otherLam,allPorts⟩ := site.selected_beta_source_ports initial matching
  have sameApp : other.app=edge.app := otherApp.trans actualApp.symm
  have sameLam : other.lam=edge.lam := otherLam.trans actualLam.symm
  apply selection.selected_route_walk initial matching _ route
  intro degree appId lamId selected middle
  obtain ⟨sameDegree,ports⟩ := allPorts selected middle
  exact ⟨sameDegree,ports.rebase_nodes sameApp sameLam⟩

/-- Every actual successful-chain member receives an image for its SAME ECR
producer, including arbitrary compound labels and arbitrary OLD histories. -/
theorem EvaluatedChainResiduals.fixed_producer_source_route_image
    {root : B} {source target localTarget : LTerm} {ps : List Path} {marked : Marked}
    (matching : Matches site.net root source.erase)
    (old : Marked.RelativeOldHistory (site.betaSyntaxFiber root source.erase) ps
      (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (localHistory : History ps (initLabels source.erase) localTarget)
    {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {selection : SourceEdgeSelection (initLabels source.erase) site.net root}
    {targetSelection : OccurrenceFragmentSelection target site.reduce root}
    {start : Path} {es : List Path} {chain : PrerequisiteChain target start es}
    (out : EvaluatedChainResiduals site (localTarget:=localTarget)
      edge selection targetSelection chain) :
    ∀member : {p : Path //p∈es},∃ctx finish,
      SourceRouteImage (initLabels source.erase) root edge ctx (out.node member).label finish
        (selection.evalLabel edge (out.node member).label) := by
  intro member
  obtain ⟨ctx,finish,route⟩ := InteriorSourceBlock.actual_old_node_route old localHistory (out.lookup member)
  have basisMatching : Matches site.net root (initLabels source.erase).erase := by
    simpa only [erase_initLabels] using matching
  have actualRoute : SelectedSourceRoute (sourceEdges [] .external (initLabels source.erase))
      (SelectedDegree (initLabels source.erase) (site.betaSyntaxFiber root (initLabels source.erase).erase))
      ctx (out.node member).label finish := by
    simpa only [erase_initLabels] using route
  obtain ⟨walk,equation⟩ := site.fixed_producer_route_walk (init_is_INIT source.erase)
    basisMatching geometry selection actualRoute
  exact ⟨ctx,finish,equation ▸ walk.image⟩

end
#print axioms BetaSourcePorts.rebase_nodes
#print axioms PathSite.fixed_producer_route_walk
#print axioms EvaluatedChainResiduals.fixed_producer_source_route_image
end Lamping.AG
