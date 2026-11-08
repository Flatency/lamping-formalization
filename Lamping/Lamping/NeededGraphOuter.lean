import Lamping.Lamping.SelectedLORound
import Lamping.Lambda.ExecutableLONormalizer

namespace Lamping.AG
open Graph Lambda Lambda.Labelled Readback ExposureScheduling

namespace Readback

/-- Histories and labels are hidden in Prop, while the outer loop stores the
actual executable graph. Both histories retain the same original INIT. -/
def StrategyGraphInvariant (original : LTerm)
    (graph : ExecutableNet (Boundary original.erase)) : Prop :=
  ∃ (current : LTerm) (schemas : List Schema)
    (raw prior : ParallelHistory original.erase current.erase),
    LabelledGraphProjection (ActualNet.initial original.erase) graph.graph (.inl ())
      schemas original current raw ∧
    raw.derivation = prior.derivation ∧ CompleteDerivation prior ∧ CallByNeedHistory prior ∧
    AuxExposureDomain graph.graph (.inl ()) current.erase initialBoundaryPolarity

theorem StrategyGraphInvariant.readbackDomain {original : LTerm}
    {graph : ExecutableNet (Boundary original.erase)}
    (invariant : StrategyGraphInvariant original graph) : ReadbackDomain graph.graph.net (.inl ()) := by
  obtain ⟨_, _, _, _, _, _, _, _, domain⟩ := invariant
  exact domain.readbackDomain

theorem StrategyGraphInvariant.initial (original : LTerm) (closed : Closed original.erase) :
    StrategyGraphInvariant original (ExecutableNet.initial original.erase) := by
  refine ⟨original, [], .nil _, .nil _, .iso (.refl _), rfl, .nil _, ?_, ?_⟩
  · intro _ _ _ earlier step tail impossible
    cases earlier <;> cases impossible
  · exact ⟨(encode_closed_independence original.erase closed 0).rootInputs,
      encode_closed_matches original.erase closed 0, encode_closed_transparency original.erase closed 0,
      encode_flowBalance original.erase 0, rfl, boundaryDepthAt 0, rfl, encode_indexed_balance original.erase 0⟩

section
variable {original : LTerm} [DecidableEq (Boundary original.erase)]

structure NeededGraphState (original : LTerm) [DecidableEq (Boundary original.erase)] where
  graph : ExecutableNet (Boundary original.erase)
  invariant : StrategyGraphInvariant original graph
  normalizable : HasNF (graph.readback (.inl ()) invariant.readbackDomain)

def NeededGraphState.term (state : NeededGraphState original) : Term :=
  state.graph.readback (.inl ()) state.invariant.readbackDomain

/-- The rank reads the current actual graph and uses only HasNF as proof of
accessibility. Administrative exposure steps are not charged this descent. -/
def NeededGraphState.order (original : LTerm) [DecidableEq (Boundary original.erase)] :
    WellFoundedRelation (NeededGraphState original) where
  rel := InvImage NeededParallelNext NeededGraphState.term
  wf := ⟨fun state => InvImage.accessible NeededGraphState.term state.normalizable.acc_neededParallelNext⟩

def NeededGraphState.initial (original : LTerm) [DecidableEq (Boundary original.erase)]
    (closed : Closed original.erase) (normalizable : HasNF original.erase) :
    NeededGraphState original := by
  let graph := ExecutableNet.initial original.erase
  have invariant := StrategyGraphInvariant.initial original closed
  refine ⟨graph, invariant, ?_⟩
  rw [graph.readback_eq_of_matches (.inl ()) invariant.readbackDomain
    (encode_closed_matches original.erase closed 0)]
  exact normalizable

end

#print axioms Lamping.AG.Readback.StrategyGraphInvariant.initial
#print axioms Lamping.AG.Readback.NeededGraphState.order
#print axioms Lamping.AG.Readback.NeededGraphState.initial

end Readback
end Lamping.AG
