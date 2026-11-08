import Lamping.Lamping.GlobalGraphSteps
import Lamping.Lamping.NetIsoInvariantTransport
import Lamping.Lamping.InitialFullIndependence
namespace Lamping.AG
open Graph Lambda

theorem GraphTrace.empty_iso {B : Type} [FiniteNames B] {g h : ActualNet B}
    (trace : GraphTrace g h []) : Nonempty (NetIso g.net h.net) := by
  cases trace with
  | iso same => exact ⟨same⟩

/-- The real zero-rewrite base includes boundary-fixed carrier renamings.
Positive rewrite traces still require the separate preservation theorem. -/
theorem initial_empty_trace_invariants (t : Term) (closed : Closed t)
    (target : ActualNet (Boundary t)) (trace : GraphTrace (ActualNet.initial t) target []) :
    Matches target.net (.inl ()) t ∧OrdinaryPathInvariants target.net (.inl ()) := by
  obtain ⟨iso⟩ := trace.empty_iso
  exact ⟨iso.matches (encode_closed_matches t closed 0),
    iso.ordinaryInvariants (encode_closed_ordinary_invariants t closed 0)⟩
end Lamping.AG
