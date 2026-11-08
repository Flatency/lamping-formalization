import Lamping.Lamping.CancellationIndependence
import Lamping.Lamping.CancellationTransparency
import Lamping.Lamping.IndependenceNesting
namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- The complete ordinary I/N/T bundle is preserved by each actual standard
cancellation. This theorem does not include Matches or other schemas. -/
theorem PathSite.cancellation_ordinary_invariants (cancel : IsCancellation s)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (root : B) (positive : boundary root=true) (old : OrdinaryPathInvariants site.net root) :
    OrdinaryPathInvariants site.reduce root := by
  have independence := site.cancellation_independence cancel flow root positive old.independence
  exact ⟨independence,independence.nesting,
    site.cancellation_transparency cancel flow root positive old.transparency⟩
end

section
variable {B : Type} [FiniteNames B] {boundary : B → Bool} {root : B}

theorem GraphStep.cancellation_transparency {s : Schema} {g h : ActualNet B}
    (step : GraphStep s g h) (cancel : IsCancellation s)
    (flow : FlowBalance g.net boundary) (positive : boundary root=true)
    (old : Transparency g.net root) : Transparency h.net root := by
  cases step with
  | atSite kept site sourceIso targetIso =>
    exact targetIso.transparency (site.cancellation_transparency cancel
      (sourceIso.flowBalance flow) root positive (sourceIso.transparency old))

theorem GraphStep.cancellation_ordinary_invariants {s : Schema} {g h : ActualNet B}
    (step : GraphStep s g h) (cancel : IsCancellation s)
    (flow : FlowBalance g.net boundary) (positive : boundary root=true)
    (old : OrdinaryPathInvariants g.net root) : OrdinaryPathInvariants h.net root := by
  cases step with
  | atSite kept site sourceIso targetIso =>
    exact targetIso.ordinaryInvariants (site.cancellation_ordinary_invariants cancel
      (sourceIso.flowBalance flow) root positive (sourceIso.ordinaryInvariants old))

theorem GraphTrace.cancellation_ordinary_invariants {g h : ActualNet B} {schemas : List Schema}
    (trace : GraphTrace g h schemas) (cancels : ∀ s∈schemas,IsCancellation s)
    (flow : FlowBalance g.net boundary) (positive : boundary root=true)
    (old : OrdinaryPathInvariants g.net root) : OrdinaryPathInvariants h.net root := by
  induction trace with
  | iso same => exact same.ordinaryInvariants old
  | cons step tail ih =>
    obtain ⟨changedFlow⟩ := step.flowBalance flow
    exact ih (fun s mem => cancels s (List.mem_cons_of_mem _ mem)) changedFlow
      (step.cancellation_ordinary_invariants (cancels _ (by simp)) flow positive old)
end

/-- Full ordinary invariants for closed initial graphs along actual finite
cancellation-only traces. This is a restricted trace result, not full SND. -/
theorem initial_cancellation_trace_ordinary_invariants (t : Term) (closed : Closed t)
    (target : ActualNet (Boundary t)) (schemas : List Schema)
    (trace : GraphTrace (ActualNet.initial t) target schemas)
    (cancels : ∀ s∈schemas,IsCancellation s) : OrdinaryPathInvariants target.net (.inl ()) := by
  obtain ⟨flow⟩ := encode_flowBalance t 0
  exact trace.cancellation_ordinary_invariants cancels flow rfl
    (encode_closed_ordinary_invariants t closed 0)
end Lamping.AG
