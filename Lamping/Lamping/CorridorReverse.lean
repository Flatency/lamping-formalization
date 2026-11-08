import Lamping.Lamping.TransparentCorridors
import Lamping.Lamping.ControlPrincipalPrefixes
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Reverse the supplied physical corridor by reversing each actual segment.
The endpoint ports are swapped; no new walk or path extension is introduced. -/
def TransparentCorridor.reverse (route : TransparentCorridor g) : TransparentCorridor g where
  first := route.last
  last := route.first
  edges := reverseEdges route.edges
  start := by
    simp only [reverseEdges,List.head?_map,List.head?_reverse,route.finish,Option.map_some,Pairing.involutive]
  finish := by
    simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,route.start,Option.map_some]
  transparent := transparent_reverse_turns route.edges route.transparent
end
end Lamping.AG
