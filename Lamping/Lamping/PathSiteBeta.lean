import Lamping.Lamping.InternalRoutes
import Lamping.Lamping.ExpandedPaths
namespace Lamping.AG
open Graph
section
variable {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {s : Schema} {kept : K → Label signature}

/-- The actual ambient endpoint corresponding to an internal partition end. -/
def PathSite.internalEnd (a : PathSite s kept (B:=B) (W:=W) (V:=V))
    (x : Bool ⊕ (V × Bool)) : Endpoint a.net :=
  (fragmentEnd (ambientLabel s kept) (pathPartition s V)).invFun (.inr x)

theorem PathSite.internalEnd_wire (a : PathSite s kept (B:=B) (W:=W) (V:=V))
    (x : Bool ⊕ (V × Bool)) :
    a.net.wire (a.internalEnd x) = a.internalEnd (a.internal x) := by
  let e := fragmentEnd (B:=B) (W:=W) (ambientLabel s kept) (pathPartition s V)
  have h := congrArg e.invFun (a.wiring x)
  change e.invFun (e (a.wire (e.invFun (.inr x))))=e.invFun (.inr (a.internal x)) at h
  simpa only [e.left_inv] using h

/-- Every existing beta PathSite supplies a genuine BetaEdge, including an
arbitrarily subdivided principal wire. The route is derived from the internal
pairing and its connectivity; it is not an extra matching certificate. -/
theorem PathSite.betaEdge_exists (a : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V)) :
    Nonempty (BetaEdge a.net) := by
  obtain ⟨es,start,finish,turns⟩ := (a.connected (.inl true)).principal_route.realize
  refine ⟨{
    app := .inr (.inl ())
    lam := .inr (.inr ())
    index := i
    appLabel := rfl
    lamLabel := rfl
    appFun := .inl ()
    appCtx := .inr false
    appArg := .inr true
    lamCtx := .inl ()
    lamBody := .inr true
    lamBind := .inr false
    appFun_role := HEq.rfl
    appCtx_role := HEq.rfl
    appArg_role := HEq.rfl
    lamCtx_role := HEq.rfl
    lamBody_role := HEq.rfl
    lamBind_role := HEq.rfl
    principal := es.map a.internalEnd
    principalStart := ?_
    principalEnd := ?_
    transparent := ?_
  }⟩
  · rw [List.head?_map,start]
    rfl
  · rw [List.getLast?_map,finish]
    change some (a.internalEnd (a.internal (.inl true))) = some (a.net.wire (a.internalEnd (.inl true)))
    rw [a.internalEnd_wire]
  · intro e f mem
    rw [←List.map_tail,List.zip_map] at mem
    obtain ⟨⟨x,y⟩,hxy,eq⟩ := List.mem_map.mp mem
    cases eq
    obtain ⟨v,d,hx,hy⟩ := turns x y hxy
    refine ⟨.inr v,d,?_,?_⟩
    · rw [a.internalEnd_wire,hx]
      rfl
    · rw [hy]
      rfl
end
end Lamping.AG
