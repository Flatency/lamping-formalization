import Lamping.Lamping.ControlOnlyConnections
import Lamping.Lamping.MatchingBetaFiber
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
private theorem control_next {e f : Endpoint g}
    (turn : ControlOnlyTurn (g:=g) e f)
    (arrives : g.wire e=.inr (.inr (w,d))) : f=.inr (.inr (w,!d)) := by
  rcases turn with ⟨v,c,entry,exit⟩ | ⟨node,p,q,op,shape,control,entry,exit⟩
  · have equal := Sum.inr.inj (Sum.inr.inj (arrives.symm.trans entry))
    cases equal
    exact exit
  · rw [arrives] at entry
    cases entry
private theorem control_cannot_enter_lambda {e f : Endpoint g}
    {node : N} {port : Port (g.label node).sort}
    (shape : (g.label node).sort=.op .lam) (arrives : g.wire e=.inl ⟨node,port⟩) :
    ¬ControlOnlyTurn (g:=g) e f := by
  rintro (⟨v,c,entry,exit⟩ | ⟨n,p,q,op,sort,control,entry,exit⟩)
  · rw [arrives] at entry; cases entry
  · have nodes := congrArg Sigma.fst (Sum.inl.inj (arrives.symm.trans entry))
    change node=n at nodes
    subst n
    rw [shape] at sort
    have equal := Kind.op.inj sort
    subst op
    rcases control with impossible | impossible | impossible <;> cases impossible
private theorem transparent_control_lists {reference actual : List (Endpoint g)}
    {node : N} {port : Port (g.label node).sort}
    (shape : (g.label node).sort=.op .lam)
    (first : reference.head?=actual.head?) (nonempty : reference≠[])
    (referenceEnd : reference.getLast?=some (g.wire (.inl ⟨node,port⟩)))
    (actualEnd : actual.getLast?=some (g.wire (.inl ⟨node,port⟩)))
    (transparent : ∀ e f,(e,f)∈reference.zip reference.tail →
      ∃ w d,g.wire e=.inr (.inr (w,d)) ∧ f=.inr (.inr (w,!d)))
    (controls : ∀ e f,(e,f)∈actual.zip actual.tail →ControlOnlyTurn (g:=g) e f) : actual=reference := by
  induction reference generalizing actual with
  | nil => exact False.elim (nonempty rfl)
  | cons e rest ih =>
    cases actual with
    | nil => cases first
    | cons a tail =>
      have same : e=a := Option.some.inj first
      subst a
      cases rest with
      | nil =>
        have endEq : e=g.wire (.inl ⟨node,port⟩) := Option.some.inj referenceEnd
        cases tail with
        | nil => rfl
        | cons f tail =>
          have turn := controls e f (by simp)
          have arrives : g.wire e=.inl ⟨node,port⟩ := by rw [endEq,g.wire.involutive]
          exact False.elim (control_cannot_enter_lambda shape arrives turn)
      | cons f rest =>
        obtain ⟨w,d,arrives,exit⟩ := transparent e f (by simp)
        cases tail with
        | nil =>
          have endEq : e=g.wire (.inl ⟨node,port⟩) := Option.some.inj actualEnd
          rw [endEq,g.wire.involutive] at arrives
          cases arrives
        | cons h tail =>
          have next := control_next (controls e h (by simp)) arrives
          have same : h=f := next.trans exit.symm
          clear next exit
          subst h
          have remaining : f::tail=f::rest := ih (actual:=f::tail) rfl (by simp)
            (by simpa only [List.getLast?_cons,Option.some_or] using referenceEnd)
            (by simpa only [List.getLast?_cons,Option.some_or] using actualEnd)
            (by intro x y pair; exact transparent x y (List.mem_cons_of_mem _ pair))
            (by intro x y pair; exact controls x y (List.mem_cons_of_mem _ pair))
          exact congrArg (e::·) remaining
private theorem same_role_endpoint {T : Type} {canonical : T} {n m : N}
    {p : Port (g.label n).sort} {q : Port (g.label m).sort}
    (nodes : n=m) (left : HEq p canonical) (right : HEq q canonical) :
    (.inl ⟨n,p⟩ : Endpoint g)=.inl ⟨m,q⟩ := by
  subst m
  have ports := eq_of_heq (left.trans right.symm)
  cases ports
  rfl
/-- A genuine redex connection with the same physical pair as a supplied
beta edge follows its entire actual transparent principal route. Equality is
proved turn by turn, not inferred from endpoint equality alone. -/
theorem RedexConnection.beta_principal_unique (connection : RedexConnection g)
    (beta : BetaEdge g) (app : connection.app=beta.app) (lam : connection.lam=beta.lam) :
    connection.edges=beta.principal := by
  have source := same_role_endpoint app connection.appPrincipal beta.appFun_role
  have target := same_role_endpoint lam connection.lamPrincipal beta.lamCtx_role
  apply transparent_control_lists (congrArg Label.sort beta.lamLabel)
    (beta.principalStart.trans ((congrArg some source).symm.trans connection.start.symm))
    (by intro empty; have first := beta.principalStart; rw [empty] at first; cases first)
    beta.principalEnd
    (by simpa only [target] using connection.finish)
    beta.transparent connection.control_only
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
/-- Preserve the distinguished physical pair when deriving a site's actual
transparent beta edge from its internal pairing. -/
theorem PathSite.distinguished_betaEdge_exists
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V)) :
    ∃ beta : BetaEdge site.net,beta.app=.inr (.inl ()) ∧ beta.lam=.inr (.inr ()) := by
  obtain ⟨es,start,finish,turns⟩ := (site.connected (.inl true)).principal_route.realize
  refine ⟨{
    app := .inr (.inl ()),lam := .inr (.inr ()),index := i
    appLabel := rfl,lamLabel := rfl
    appFun := .inl (),appCtx := .inr false,appArg := .inr true
    lamCtx := .inl (),lamBody := .inr true,lamBind := .inr false
    appFun_role := HEq.rfl,appCtx_role := HEq.rfl,appArg_role := HEq.rfl
    lamCtx_role := HEq.rfl,lamBody_role := HEq.rfl,lamBind_role := HEq.rfl
    principal := es.map site.internalEnd
    principalStart := ?_,principalEnd := ?_,transparent := ?_ },rfl,rfl⟩
  · rw [List.head?_map,start]; rfl
  · rw [List.getLast?_map,finish]
    change some (site.internalEnd (site.internal (.inl true))) =
      some (site.net.wire (site.internalEnd (.inl true)))
    rw [site.internalEnd_wire]
  · intro e f member
    rw [←List.map_tail,List.zip_map] at member
    obtain ⟨⟨x,y⟩,pair,equal⟩ := List.mem_map.mp member
    cases equal
    obtain ⟨v,d,entry,exit⟩ := turns x y pair
    refine ⟨.inr v,d,?_,?_⟩
    · rw [site.internalEnd_wire,entry]; rfl
    · rw [exit]; rfl
/-- A fixed actual graph beta site has one literal principal route for all
source syntax redexes in its actual physical fiber, including distinct copies.
The finite route is derived from the site, not provided as a fiber field. -/
theorem PathSite.beta_fiber_principal
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {t : Term} (matching : Matches site.net root t) :
    ∃ beta : BetaEdge site.net,beta.app=.inr (.inl ()) ∧ beta.lam=.inr (.inr ()) ∧
      ∀ (redex : RedexOcc t) (source : ActualRedexAccess site.net root redex),
      redex.val∈site.betaSyntaxFiber root t → source.connection.edges=beta.principal := by
  obtain ⟨beta,app,lam⟩ := site.distinguished_betaEdge_exists
  refine ⟨beta,app,lam,?_⟩
  intro redex source member
  have physical := (source.physical_selection_iff site.net root t (.inr (.inl ()))
    (.inr (.inr ())) matching).mp member
  exact source.connection.beta_principal_unique beta (physical.1.trans app.symm) (physical.2.trans lam.symm)
end
end Lamping.AG


