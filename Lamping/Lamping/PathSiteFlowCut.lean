import Lamping.Lamping.FlowCompositional
import Lamping.Lamping.InternalRoutes
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V)) {boundary : B → Bool}

def PathSite.frontierFlow (old : FlowBalance site.net boundary) : s.Frontier → Bool :=
  Sum.elim
    (fun a => !(flowPort (.op s.active) (old.nodes (.inr (.inl ()))) (.inr a)))
    (fun a => !(flowPort (.op s.passive) (old.nodes (.inr (.inr ()))) (.inr a)))

private theorem cut_flow (old : FlowBalance site.net boundary)
    (e : Endpoint (cutFragment site.net (pathPartition s V) site.closed)) :
    flowEndpoint site.net old.nodes boundary old.vertices
      ((fragmentEnd site.net.label (pathPartition s V)).invFun (.inl e)) =
    flowEndpoint (cutFragment site.net (pathPartition s V) site.closed)
      (fun k => old.nodes (.inl k)) (Sum.elim boundary (fun f => !(site.frontierFlow old f)))
      (fun w => old.vertices (.inl w)) e := by
  rcases e with ⟨k,p⟩ | ((b | (a|a)) | ⟨w,d⟩)
  · rfl
  · rfl
  · change flowPort (.op s.active) (old.nodes (.inr (.inl ()))) (.inr a) = !(!(flowPort (.op s.active) (old.nodes (.inr (.inl ()))) (.inr a)))
    simp
  · change flowPort (.op s.passive) (old.nodes (.inr (.inr ()))) (.inr a) = !(!(flowPort (.op s.passive) (old.nodes (.inr (.inr ()))) (.inr a)))
    simp
  · rfl

def PathSite.cut_flowBalance (old : FlowBalance site.net boundary) :
    FlowBalance (cutFragment site.net (pathPartition s V) site.closed)
      (Sum.elim boundary (fun f => !(site.frontierFlow old f))) where
  nodes := fun k => old.nodes (.inl k)
  vertices := fun w => old.vertices (.inl w)
  wiring e := by
    let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition s V)
    have restricted := restrict_mate (site.net.wire.rename split) site.closed e
    have pulled := congrArg split.invFun restricted
    simp only [Pairing.rename,split.left_inv] at pulled
    change site.net.wire (split.invFun (.inl e)) =
      split.invFun (.inl ((cutFragment site.net (pathPartition s V) site.closed).wire e)) at pulled
    have opposite := old.wiring (split.invFun (.inl e))
    rw [pulled] at opposite
    rw [cut_flow,cut_flow] at opposite
    exact opposite

def PathSite.internalFlow (old : FlowBalance site.net boundary) (i : Bool⊕(V×Bool)) : Bool :=
  flowEndpoint site.net old.nodes boundary old.vertices
    ((fragmentEnd site.net.label (pathPartition s V)).invFun (.inr i))

theorem PathSite.internal_segment_flow (old : FlowBalance site.net boundary) (i : Bool⊕(V×Bool)) :
    site.internalFlow old (site.internal i) = !(site.internalFlow old i) := by
  let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition s V)
  have paired := congrArg split.invFun (site.wiring i)
  change split.invFun ((site.net.wire.rename split) (.inr i)) = _ at paired
  simp only [Pairing.rename,split.left_inv] at paired
  change site.net.wire (split.invFun (.inr i)) = split.invFun (.inr (site.internal i)) at paired
  have opposite := old.wiring (split.invFun (.inr i))
  rw [paired] at opposite
  exact opposite

theorem PathSite.internal_vertex_flow (old : FlowBalance site.net boundary) (v : V) (d : Bool) :
    site.internalFlow old (.inr (v,!d)) = !(site.internalFlow old (.inr (v,d))) := by
  change (if !d then !(old.vertices (.inr v)) else old.vertices (.inr v)) =
    !(if d then !(old.vertices (.inr v)) else old.vertices (.inr v))
  cases d <;> simp

/-- Follow the genuine alternating principal route. General internal graph
connectivity alone does not count its flips; each wire and vertex is retained. -/
theorem PathSite.internal_route_flow (old : FlowBalance site.net boundary)
    {y : Bool⊕(V×Bool)} (route : PrincipalRoute site.internal y) :
    site.internalFlow old y = !(site.internalFlow old (.inl false)) := by
  induction route with
  | single => exact site.internal_segment_flow old _
  | @snoc v d route ih =>
    rw [site.internal_segment_flow,site.internal_vertex_flow]
    simpa using ih

theorem PathSite.principal_flow (old : FlowBalance site.net boundary) :
    flowPort (.op s.passive) (old.nodes (.inr (.inr ()))) (.inl ()) =
      !(flowPort (.op s.active) (old.nodes (.inr (.inl ()))) (.inl ())) :=
  site.internal_route_flow old ((site.connected (.inl true)).principal_route)

def PathSite.left_flowBalance (old : FlowBalance site.net boundary) :
    FlowBalance s.left (site.frontierFlow old) where
  nodes := fun n => old.nodes (.inr n)
  vertices := Empty.elim
  wiring := by
    rintro (⟨u|u,p⟩ | ((a|a) | ⟨w,d⟩))
    · cases u
      cases p with
      | inl u => cases u; exact site.principal_flow old
      | inr a => rfl
    · cases u
      cases p with
      | inl u =>
        cases u
        change flowPort (.op s.active) (old.nodes (.inr (.inl ()))) (.inl ()) =
          !(flowPort (.op s.passive) (old.nodes (.inr (.inr ()))) (.inl ()))
        rw [site.principal_flow]
        simp
      | inr a => rfl
    · change flowPort (.op s.active) (old.nodes (.inr (.inl ()))) (.inr a) =
        !(!(flowPort (.op s.active) (old.nodes (.inr (.inl ()))) (.inr a)))
      simp
    · change flowPort (.op s.passive) (old.nodes (.inr (.inr ()))) (.inr a) =
        !(!(flowPort (.op s.passive) (old.nodes (.inr (.inr ()))) (.inr a)))
      simp
    · exact nomatch w
end
end Lamping.AG
