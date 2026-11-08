import Lamping.Lamping.ComputedFocusCorridorEndpoints
import Lamping.Lamping.TransparentCorridors

namespace Lamping.AG.ExposureScheduling
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Equip the already computed SAME fields with their proved geometry.
No endpoint, route or recipe is chosen from a semantic existence proof. -/
def FocusCorridorData.toTransparentCorridor (connection : RedexConnection g)
    (focus : PhysicalControlFocus g)
    (chosen : selectPhysicalControlFocus g connection.edges=some focus)
    (data : FocusCorridorData g) (computed : computeFocusCorridorData connection focus=some data) :
    TransparentCorridor g where
  first := data.first
  last := data.last
  edges := data.edges
  start := (computeFocusCorridorData_endpoints connection focus chosen data computed).1
  finish := (computeFocusCorridorData_endpoints connection focus chosen data computed).2
  transparent := by
    have actual := computeFocusCorridorData_edges connection focus data computed
    rw [actual]
    exact selectPhysicalControlFocus_skipped_transparent connection focus chosen
end
end Lamping.AG.ExposureScheduling
