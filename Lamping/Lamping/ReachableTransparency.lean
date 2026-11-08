import Lamping.Lamping.IndexedBetaTransparency
import Lamping.Lamping.ActionTransparency
import Lamping.Lamping.CancellationInvariantPreservation
import Lamping.Lamping.GraphIndexedBalance
import Lamping.Lamping.InitialTransparency
namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- Every actual schema preserves ordinary same-assignment Transparency using
only source T and structural invariants. No full Independence is required. -/
theorem PathSite.transparency_indexed {boundary : B → Bool} {heights : B → Int}
    (flow : FlowBalance site.net boundary) (root : B) (positive : boundary root=true)
    (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (oldT : Transparency site.net root) : Transparency site.reduce root := by
  cases s with
  | beta i => exact site.beta_transparency_indexed flow root positive balance rootDepth oldT
  | fanCancel i => exact site.cancellation_transparency (.fan i) flow root positive oldT
  | croCancel i => exact site.cancellation_transparency (.cro i) flow root positive oldT
  | braCancel i => exact site.cancellation_transparency (.bra i) flow root positive oldT
  | fanAction f i j lt => exact site.action_transparency (.fan f i j lt) flow root positive oldT
  | croAction f i j lt => exact site.action_transparency (.cro f i j lt) flow root positive oldT
  | braAction f i j lt => exact site.action_transparency (.bra f i j lt) flow root positive oldT
end
section
variable {B : Type} [FiniteNames B] {boundary : B → Bool} {heights : B → Int} {root : B}

theorem GraphStep.transparency_indexed {s : Schema} {g h : ActualNet B} (step : GraphStep s g h)
    (flow : FlowBalance g.net boundary) (positive : boundary root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (oldT : Transparency g.net root) : Transparency h.net root := by
  cases step with
  | atSite kept site sourceIso targetIso =>
    exact targetIso.transparency (site.transparency_indexed (sourceIso.flowBalance flow) root positive
      (sourceIso.indexed_balance balance) rootDepth (sourceIso.transparency oldT))

/-- Actual finite traces preserve T. Each cons step obtains its structural
witnesses from the real source graph and schema, rather than assuming the
invariants for intermediate graphs. Zero steps include actual carrier isos. -/
theorem GraphTrace.transparency_indexed {g h : ActualNet B} {schemas : List Schema}
    (trace : GraphTrace g h schemas) (flow : FlowBalance g.net boundary) (positive : boundary root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (oldT : Transparency g.net root) : Transparency h.net root := by
  induction trace with
  | iso same => exact same.transparency oldT
  | cons step tail ih =>
    obtain ⟨newFlow⟩ := step.flowBalance flow
    obtain ⟨newBalance⟩ := step.indexed_balance balance
    exact ih newFlow newBalance (step.transparency_indexed flow positive balance rootDepth oldT)
end

/-- The ordinary Transparency property holds in every graph reached by any
actual finite standard-AG rewrite trace from a Closed initial encoding. The
original assignment, binder and ordered prefix/loop decomposition are retained.
No general proper-source I, RootInputs, Matches or soundness is a premise. -/
theorem initial_trace_transparency (t : Term) (closed : Closed t)
    (target : ActualNet (Boundary t)) (schemas : List Schema)
    (trace : GraphTrace (ActualNet.initial t) target schemas) : Transparency target.net (.inl ()) := by
  obtain ⟨flow⟩ := encode_flowBalance t 0
  obtain ⟨balance⟩ := encode_indexed_balance t 0
  exact trace.transparency_indexed flow rfl balance rfl (encode_closed_transparency t closed 0)
end Lamping.AG
