import Lamping.Lamping.RootBetaInputs
import Lamping.Lamping.RootActionTypedInputs
import Lamping.Lamping.RootCancellationInputs
namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- All seven actual rules preserve root-input existence from their proved
source hypotheses. Source Matches is needed by the action branches. This
is a step theorem; trace closure still requires actual Matches preservation. -/
theorem PathSite.reduce_rootInputs
    {directions : B → Bool} {heights : B → Int} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true)
    (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs site.net root) (oldT : Transparency site.net root)
    {t : Term} (matching : Matches site.net root t) : RootInputs site.reduce root := by
  cases s with
  | beta i => exact site.beta_rootInputs flow root positive balance rootDepth inputs oldT
  | fanCancel i => exact site.cancellation_rootInputs (.fan i) flow root positive inputs
  | croCancel i => exact site.cancellation_rootInputs (.cro i) flow root positive inputs
  | braCancel i => exact site.cancellation_rootInputs (.bra i) flow root positive inputs
  | fanAction f i j lt =>
    exact site.action_rootInputs (.fan f i j lt) flow root positive balance rootDepth matching inputs oldT
  | croAction f i j lt =>
    exact site.action_rootInputs (.cro f i j lt) flow root positive balance rootDepth matching inputs oldT
  | braAction f i j lt =>
    exact site.action_rootInputs (.bra f i j lt) flow root positive balance rootDepth matching inputs oldT
end
section
variable {B : Type} [FiniteNames B]

/-- Boundary-fixing source/target isomorphisms transport the actual step
theorem. No invariants are fields of GraphStep or ActualNet. -/
theorem GraphStep.rootInputs {s : Schema} {g h : ActualNet B} (step : GraphStep s g h)
    {directions : B → Bool} {heights : B → Int} {root : B}
    (flow : FlowBalance g.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (oldT : Transparency g.net root)
    {t : Term} (matching : Matches g.net root t) : RootInputs h.net root := by
  cases step with
  | atSite kept site sourceIso targetIso =>
    exact targetIso.rootInputs (site.reduce_rootInputs (sourceIso.flowBalance flow) root positive
      (sourceIso.indexed_balance balance) rootDepth (sourceIso.rootInputs inputs)
      (sourceIso.transparency oldT) (sourceIso.matches matching))
end
end Lamping.AG
