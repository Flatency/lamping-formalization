import Lamping.Lamping.BetaTransparency
import Lamping.Lamping.ActionTransparency
import Lamping.Lamping.CancellationInvariantPreservation
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- All seven physical schemas preserve ordinary T, with ordinary I needed
only by the beta paired-stream proof. This is one-step preservation, not a
trace theorem supplied without preservation of full I. -/
theorem PathSite.transparency {boundary : B → Bool}
    (flow : FlowBalance site.net boundary) (root : B) (positive : boundary root=true)
    (oldI : Independence site.net root) (oldT : Transparency site.net root) : Transparency site.reduce root := by
  cases s with
  | beta i => exact site.beta_transparency flow root positive oldI oldT
  | fanCancel i => exact site.cancellation_transparency (.fan i) flow root positive oldT
  | croCancel i => exact site.cancellation_transparency (.cro i) flow root positive oldT
  | braCancel i => exact site.cancellation_transparency (.bra i) flow root positive oldT
  | fanAction f i j lt => exact site.action_transparency (.fan f i j lt) flow root positive oldT
  | croAction f i j lt => exact site.action_transparency (.cro f i j lt) flow root positive oldT
  | braAction f i j lt => exact site.action_transparency (.bra f i j lt) flow root positive oldT
end

section
variable {B : Type} [FiniteNames B] {boundary : B → Bool} {root : B}

theorem GraphStep.transparency {s : Schema} {g h : ActualNet B} (step : GraphStep s g h)
    (flow : FlowBalance g.net boundary) (positive : boundary root=true)
    (oldI : Independence g.net root) (oldT : Transparency g.net root) : Transparency h.net root := by
  cases step with
  | atSite kept site sourceIso targetIso =>
    exact targetIso.transparency (site.transparency (sourceIso.flowBalance flow) root positive
      (sourceIso.independence oldI) (sourceIso.transparency oldT))
end
end Lamping.AG
