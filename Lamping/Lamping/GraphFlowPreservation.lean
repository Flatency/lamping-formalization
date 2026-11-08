import Lamping.Lamping.PathSiteFlowCut
import Lamping.Lamping.FlowSchemaPreservation
import Lamping.Lamping.GlobalGraphSteps
import Lamping.Lamping.NetIsoPathTransport
namespace Lamping.Graph
open Lamping.AG

private theorem flow_port_heq (x y : Label signature) (same : y=x)
    (p : Port x.sort) (q : Port y.sort) (role : HEq q p) (base : Bool) :
    flowPort y.sort base q = flowPort x.sort base p := by
  subst y
  have equal : q=p := eq_of_heq role
  subst q
  rfl
section
variable {N M B W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames W] [FiniteNames V]
variable {g : Net signature N B W} {h : Net signature M B V} (iso : NetIso g h)

theorem NetIso.flow_image (nodes : N → Bool) (boundary : B → Bool) (vertices : W → Bool) (e : Endpoint g) :
    flowEndpoint h (fun m => nodes (iso.nodes.invFun m)) boundary (fun v => vertices (iso.vertices.invFun v))
      (iso.ends e) = flowEndpoint g nodes boundary vertices e := by
  rcases e with ⟨n,p⟩ | (b | ⟨w,d⟩)
  · rw [iso.node_end_image]
    change flowPort _ (nodes (iso.nodes.invFun (iso.nodes n))) (iso.imagePort n p) = _
    rw [iso.nodes.left_inv]
    exact flow_port_heq _ _ (iso.labels n) p _ (iso.imagePort_heq n p) (nodes n)
  · rw [iso.boundary_end]
    rfl
  · rw [iso.vertex_end]
    change (if d then !(vertices (iso.vertices.invFun (iso.vertices w))) else vertices (iso.vertices.invFun (iso.vertices w))) = _
    rw [iso.vertices.left_inv]
    rfl

def NetIso.flowBalance {boundary : B → Bool} (old : FlowBalance g boundary) : FlowBalance h boundary where
  nodes := fun m => old.nodes (iso.nodes.invFun m)
  vertices := fun v => old.vertices (iso.vertices.invFun v)
  wiring e := by
    let before := iso.ends.invFun e
    have same : iso.ends before=e := iso.ends.right_inv e
    calc
      flowEndpoint h _ _ _ (h.wire e) = flowEndpoint h _ _ _ (iso.ends (g.wire before)) := by rw [iso.wiring,same]
      _ = flowEndpoint g old.nodes boundary old.vertices (g.wire before) := iso.flow_image _ _ _ _
      _ = !(flowEndpoint g old.nodes boundary old.vertices before) := old.wiring before
      _ = !(flowEndpoint h _ _ _ e) := by rw [←same,iso.flow_image]
end
end Lamping.Graph

namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V)) {boundary : B → Bool}

/-- Whole actual cut/replacement/glue preservation. Outside aliases, transparent
vertices and each frontier occurrence are preserved by the existing operations. -/
theorem PathSite.reduce_flowBalance (old : FlowBalance site.net boundary) :
    Nonempty (FlowBalance site.reduce boundary) := by
  obtain ⟨rhs⟩ := s.flow_preservation (site.frontierFlow old) (site.left_flowBalance old)
  exact ⟨FlowBalance.plug _ _ boundary (site.frontierFlow old) (site.cut_flowBalance old) rhs⟩

/-- The constructed replacement also retains the explicit polarity of every
new glue vertex, needed when reflecting an actual reduced path. -/
theorem PathSite.reduce_flowBalance_glue (old : FlowBalance site.net boundary) :
    ∃ changed : FlowBalance site.reduce boundary,
      ∀ f, changed.vertices (.inr f) = !(site.frontierFlow old f) := by
  obtain ⟨rhs⟩ := s.flow_preservation (site.frontierFlow old) (site.left_flowBalance old)
  exact ⟨FlowBalance.plug _ _ boundary (site.frontierFlow old) (site.cut_flowBalance old) rhs,
    fun _ => rfl⟩
end
section
variable {B : Type} [FiniteNames B] {boundary : B → Bool}

theorem GraphStep.flowBalance {s : Schema} {g h : ActualNet B} (step : GraphStep s g h)
    (old : FlowBalance g.net boundary) : Nonempty (FlowBalance h.net boundary) := by
  cases step with
  | atSite kept site sourceIso targetIso =>
    obtain ⟨changed⟩ := site.reduce_flowBalance (sourceIso.flowBalance old)
    exact ⟨targetIso.flowBalance changed⟩

theorem GraphTrace.flowBalance {g h : ActualNet B} {schemas : List Schema} (trace : GraphTrace g h schemas)
    (old : FlowBalance g.net boundary) : Nonempty (FlowBalance h.net boundary) := by
  induction trace with
  | iso same => exact ⟨same.flowBalance old⟩
  | cons step tail ih =>
    obtain ⟨changed⟩ := step.flowBalance old
    exact ih changed
end

/-- Every actual finite rewrite trace from an initial encoding has a structural
flow witness. No closedness, path invariant, Matches or SND is assumed. -/
theorem initial_trace_flowBalance (t : Term) (target : ActualNet (Boundary t)) (schemas : List Schema)
    (trace : GraphTrace (ActualNet.initial t) target schemas) :
    Nonempty (FlowBalance target.net initialBoundaryPolarity) := by
  obtain ⟨initial⟩ := encode_flowBalance t 0
  exact trace.flowBalance initial
end Lamping.AG
