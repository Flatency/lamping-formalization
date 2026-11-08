import Lamping.Lamping.PhysicalCorridorPresentation
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]

/-- A supplied actual finite transparent principal corridor in any graph
constructs a real schema rewrite. All and only its W vertices are selected;
outside vertices, boundary names and other components remain in the graph. -/
theorem physical_corridor_graph_step (g : Net signature N B W) (schema : Schema)
    (route : TransparentCorridor g) (active passive : N) (different : active≠passive)
    (activeLabel : g.label active=label schema.active schema.low)
    (passiveLabel : g.label passive=label schema.passive schema.high)
    (p : Port (g.label active).sort) (q : Port (g.label passive).sort)
    (activePrincipal : HEq p (Sum.inl () : Port (.op schema.active)))
    (passivePrincipal : HEq q (Sum.inl () : Port (.op schema.passive)))
    (first : route.first=⟨active,p⟩) (last : route.last=⟨passive,q⟩) :
    ∃ target : ActualNet B,GraphStep schema (ActualNet.ofNet g) target := by
  obtain ⟨presentation⟩ := physical_corridor_presentation g schema route active passive different
    activeLabel passiveLabel p q activePrincipal passivePrincipal first last
  exact ⟨ActualNet.ofNet presentation.site.reduce,presentation.graph_step⟩
end
end Lamping.AG
