import Lamping.Lamping.MatchingSelectedDegreeRealization
import Lamping.Lambda.LabelArgumentBinderScope
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm}
/-- A physical fragment retains the actual old syntax edge and environment,
so its source-edge membership is a proved consequence of its occurrence. -/
theorem SourceEdgeFragment.source_member
    (fragment : SourceEdgeFragment original g root edge p) :
    edge∈sourceEdges [] .external original := by
  obtain ⟨env,ctx,sub,site,equal⟩ := fragment.occurrence
  rw [←equal]
  apply site.edges_subset
  cases sub <;> exact List.mem_cons_self
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
/-- Exact original selected degree membership and INIT lock an actual typed
source route to the physical function edge of the fixed graph beta site.
The resulting literal principal route has exactly the caller's source ports. -/
theorem PathSite.selected_route_principal_fragment
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original : LTerm} (initial : INIT original)
    (matching : Matches site.net root original.erase) :
    ∃ beta : BetaEdge site.net,beta.app=.inr (.inl ()) ∧ beta.lam=.inr (.inr ()) ∧
      ∀ {degree appId lamId},SelectedDegree original (site.betaSyntaxFiber root original.erase) degree →
      SourceRoute (sourceEdges [] .external original) (.appFn appId) degree (.lamContext lamId) →
      ∃ p,∃ fragment : SourceEdgeFragment original site.net root
        ⟨degree,.appFn appId,.lamContext lamId⟩ p,fragment.segments=beta.principal := by
  obtain ⟨beta,app,lam,allDegrees⟩ := site.selected_degree_principal_fragment matching
  refine ⟨beta,app,lam,?_⟩
  intro degree appId lamId selected route
  obtain ⟨name,oldApp,body,argument,member,lookup,fragment,segments⟩ := allDegrees degree selected
  obtain ⟨n,atomic⟩ := selected.atomic initial
  rw [atomic] at route
  obtain ⟨edge,edgeMember,edgeAtom,edgeFrom,edgeTo⟩ := route.initial_atom_edge initial
  have equal := sourceEdges_unique initial edgeMember fragment.source_member (edgeAtom.trans atomic.symm)
  have appEq : oldApp=appId := SourcePort.appFn.inj
    ((congrArg SourceEdge.fromPort equal).symm.trans edgeFrom)
  have lamEq : degree=lamId := SourcePort.lamContext.inj
    ((congrArg SourceEdge.toPort equal).symm.trans edgeTo)
  cases appEq
  cases lamEq
  exact ⟨name++[.fn],fragment,segments⟩
end
end Lamping.AG
