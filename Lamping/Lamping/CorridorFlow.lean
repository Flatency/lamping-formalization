import Lamping.Lamping.PhysicalCorridorSites
import Lamping.Lamping.PathSitePrincipalRoutes
import Lamping.Lamping.FlowBalance
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {boundary : B → Bool}

/-- Every actual labelled segment departure has the same structural polarity,
without requiring that polarity to be true or that the first end is a root. -/
theorem Labelling.departure_flow_endpoints {es : List (Endpoint g)} {a b : Context}
    (labels : Labelling g es a b) (flow : FlowBalance g boundary)
    (first last : Endpoint g) (head : es.head?=some first) (finish : es.getLast?=some last) :
    flowEndpoint g flow.nodes boundary flow.vertices last=
      flowEndpoint g flow.nodes boundary flow.vertices first := by
  induction labels generalizing first last with
  | single e a =>
    change some e=some first at head
    change some e=some last at finish
    have one := Option.some.inj head
    have two := Option.some.inj finish
    rw [←one,←two]
  | @cons e f es a middle b turn tail ih =>
    have same := Option.some.inj head
    subst first
    have lastTail : (f::es).getLast?=some last := by
      simpa only [List.getLast?_cons_cons] using finish
    have rest := ih f last rfl lastTail
    rw [rest,turn.flow_flip flow.nodes flow.vertices,flow.wiring]
    cases flowEndpoint g flow.nodes boundary flow.vertices e <;> rfl

/-- The actual two principal endpoints of a transparent corridor have opposite
polarity, even though the internal W route may be arbitrarily subdivided. -/
theorem TransparentCorridor.endpoint_flow (route : TransparentCorridor g) (flow : FlowBalance g boundary) :
    flowEndpoint g flow.nodes boundary flow.vertices (.inl route.last)=
      !(flowEndpoint g flow.nodes boundary flow.vertices (.inl route.first)) := by
  have nonempty : route.edges≠[] := by
    intro empty
    have start := route.start
    rw [empty] at start
    cases start
  have labels := transparent_route_labelling g route.edges nonempty route.transparent Context.empty
  have same := labels.departure_flow_endpoints flow (.inl route.first) (g.wire (.inl route.last))
    route.start route.finish
  rw [flow.wiring] at same
  have flipped := congrArg Bool.not same
  simpa only [Bool.not_not] using flipped

/-- Schema labels and actual flow automatically exclude choosing the same
physical node at both ends of an existing transparent principal corridor. -/
theorem TransparentCorridor.principal_nodes_distinct (route : TransparentCorridor g)
    (flow : FlowBalance g boundary) (schema : Schema) (active passive : N)
    (activeLabel : g.label active=label schema.active schema.low)
    (passiveLabel : g.label passive=label schema.passive schema.high)
    (p : Port (g.label active).sort) (q : Port (g.label passive).sort)
    (activePrincipal : HEq p (Sum.inl () : Port (.op schema.active)))
    (passivePrincipal : HEq q (Sum.inl () : Port (.op schema.passive)))
    (first : route.first=⟨active,p⟩) (last : route.last=⟨passive,q⟩) : active≠passive := by
  intro same
  subst passive
  have kinds := congrArg Label.sort (activeLabel.symm.trans passiveLabel)
  have ops : schema.active=schema.passive := Kind.op.inj kinds
  rw [←ops] at passivePrincipal
  have ports : p=q := eq_of_heq (activePrincipal.trans passivePrincipal.symm)
  subst q
  have opposite := route.endpoint_flow flow
  rw [first,last] at opposite
  change flowEndpoint g flow.nodes boundary flow.vertices (.inl ⟨active,p⟩)=
    !(flowEndpoint g flow.nodes boundary flow.vertices (.inl ⟨active,p⟩)) at opposite
  have noFixed (x : Bool) : x≠ !x := by cases x <;> decide
  exact noFixed _ opposite

/-- A real transparent schema corridor in a structurally balanced graph is
an actual GraphStep, with all carrier and connected-cut witnesses constructed. -/
theorem physical_corridor_graph_step_of_flow (g : Net signature N B W) (schema : Schema)
    (flow : FlowBalance g boundary) (route : TransparentCorridor g) (active passive : N)
    (activeLabel : g.label active=label schema.active schema.low)
    (passiveLabel : g.label passive=label schema.passive schema.high)
    (p : Port (g.label active).sort) (q : Port (g.label passive).sort)
    (activePrincipal : HEq p (Sum.inl () : Port (.op schema.active)))
    (passivePrincipal : HEq q (Sum.inl () : Port (.op schema.passive)))
    (first : route.first=⟨active,p⟩) (last : route.last=⟨passive,q⟩) :
    ∃ target : ActualNet B,GraphStep schema (ActualNet.ofNet g) target :=
  physical_corridor_graph_step g schema route active passive
    (route.principal_nodes_distinct flow schema active passive activeLabel passiveLabel
      p q activePrincipal passivePrincipal first last)
    activeLabel passiveLabel p q activePrincipal passivePrincipal first last
end
end Lamping.AG
