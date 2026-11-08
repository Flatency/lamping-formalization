import Lamping.Lamping.PathSiteBalanceCut
import Lamping.Lamping.SchemaBalance
import Lamping.Lamping.EncodedBalance
import Lamping.Lamping.GlobalGraphSteps
import Lamping.Lamping.NetIsoPathTransport
namespace Lamping.Graph
open Lamping.AG

private theorem port_depth_heq (x y : Label signature) (same : y=x)
    (p : Port x.sort) (q : Port y.sort) (role : HEq q p) (base : Int) :
    portDepth y.index y.sort base q=portDepth x.index x.sort base p := by
  subst y
  have equal : q=p := eq_of_heq role
  subst q
  rfl
section
variable {N M B W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames W] [FiniteNames V]
variable {g : Net signature N B W} {h : Net signature M B V} (iso : NetIso g h)

theorem NetIso.depth_image (nodes : N → Int) (boundary : B → Int) (vertices : W → Int) (e : Endpoint g) :
    endpointDepth h (fun m => nodes (iso.nodes.invFun m)) boundary (fun v => vertices (iso.vertices.invFun v))
      (iso.ends e)=endpointDepth g nodes boundary vertices e := by
  rcases e with ⟨n,p⟩ | (b | ⟨w,d⟩)
  · rw [iso.node_end_image]
    change portDepth _ _ (nodes (iso.nodes.invFun (iso.nodes n))) (iso.imagePort n p)=_
    rw [iso.nodes.left_inv]
    exact port_depth_heq _ _ (iso.labels n) p _ (iso.imagePort_heq n p) (nodes n)
  · rw [iso.boundary_end]
    rfl
  · rw [iso.vertex_end]
    exact congrArg vertices (iso.vertices.left_inv w)

def NetIso.balance {boundary : B → Int} (old : LevelBalance g boundary) : LevelBalance h boundary where
  nodes := fun m => old.nodes (iso.nodes.invFun m)
  vertices := fun v => old.vertices (iso.vertices.invFun v)
  wiring e := by
    let before := iso.ends.invFun e
    have same : iso.ends before=e := iso.ends.right_inv e
    calc
      endpointDepth h _ _ _ (h.wire e)=endpointDepth h _ _ _ (iso.ends (g.wire before)) := by rw [iso.wiring,same]
      _=endpointDepth g old.nodes boundary old.vertices (g.wire before) := iso.depth_image _ _ _ _
      _=endpointDepth g old.nodes boundary old.vertices before := old.wiring before
      _=endpointDepth h _ _ _ e := by rw [←same]; exact (iso.depth_image _ _ _ _).symm
end
end Lamping.Graph

namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V)) {boundary : B → Int}

/-- Actual cut/replacement/glue preservation, with the subdivided principal
component removed and the original outside pairing retained literally. -/
theorem PathSite.reduce_balance (old : LevelBalance site.net boundary) :
    Nonempty (LevelBalance site.reduce boundary) := by
  obtain ⟨rhs⟩ := s.balance_preservation (site.frontierDepth old) (site.left_balance old)
  exact ⟨LevelBalance.plug _ _ boundary (site.frontierDepth old) (site.cut_balance old) rhs⟩
end
section
variable {B : Type} [FiniteNames B] {boundary : B → Int}

theorem GraphStep.balance {s : Schema} {g h : ActualNet B} (step : GraphStep s g h)
    (old : LevelBalance g.net boundary) : Nonempty (LevelBalance h.net boundary) := by
  cases step with
  | atSite kept site sourceIso targetIso =>
    obtain ⟨changed⟩ := site.reduce_balance (sourceIso.balance old)
    exact ⟨targetIso.balance changed⟩

theorem GraphTrace.balance {g h : ActualNet B} {schemas : List Schema} (trace : GraphTrace g h schemas)
    (old : LevelBalance g.net boundary) : Nonempty (LevelBalance h.net boundary) := by
  induction trace with
  | iso same => exact ⟨same.balance old⟩
  | cons step tail ih =>
    obtain ⟨changed⟩ := step.balance old
    exact ih changed
end

/-- Structural balance holds along every actual finite graph rewrite trace.
No Matches, SND, beta-history completion, or scheduling assumption is used. -/
theorem initial_trace_balance (t : Term) (target : ActualNet (Boundary t)) (schemas : List Schema)
    (trace : GraphTrace (ActualNet.initial t) target schemas) :
    Nonempty (LevelBalance target.net (boundaryDepthAt 0)) := by
  obtain ⟨initial⟩ := encode_balance t 0
  exact trace.balance initial
end Lamping.AG
