import Lamping.Lamping.CancellationTypedInputs
import Lamping.Lamping.RootPathInputs
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- Actual cancellation preserves root-input totality using its genuine
constant-block ancestor and typed physical endpoint metadata. -/
theorem PathSite.cancellation_rootInputs (cancel : IsCancellation s)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (root : B) (positive : boundary root=true) (inputs : RootInputs site.net root) :
    RootInputs site.reduce root := by
  intro es input output terminal role level labels _forward rooted finish atTerminal incoming requested
  have empty : s.right.N → False := by cases cancel <;> exact Empty.elim
  obtain ⟨node,p,same⟩ := site.reduced_incoming_kept empty atTerminal incoming
  let c := cutFragment site.net (pathPartition s V) site.closed
  let r := s.right.net
  let first : Endpoint c := .inr (.inl (.inl root))
  let last : Endpoint c := c.wire (.inl ⟨node,p⟩)
  have represented : site.reduce.wire terminal=AG.plugLeft c r last := by
    rw [same]
    exact plugLeft_wire c r (.inl ⟨node,p⟩)
  have actualRole : AtProperRole site.reduce root (site.reduce.wire (AG.plugLeft c r last)) role level := by
    rw [←represented,Pairing.involutive]
    exact atTerminal
  have oldRole := site.reduced_outside_incoming root last role level actualRole incoming
  have firstHead : es.head?=some (AG.plugLeft c r first) := rooted
  have lastFinish : es.getLast?=some (AG.plugLeft c r last) := finish.trans (congrArg some represented)
  obtain ⟨old,_,oldLabels,oldHead,oldLast,replay⟩ :=
    site.cancellation_relabelling_ancestor cancel labels first last firstHead lastFinish
  have oldRoot : old.head?=some (.inr (.inl root)) := oldHead
  have oldForward := oldLabels.root_forward_of_flow flow root oldRoot positive
  have oldFinish : old.getLast?=some (site.net.wire (site.net.wire (site.outsideEnd last))) := by
    simpa only [Pairing.involutive] using oldLast
  obtain ⟨result,changed⟩ := inputs old input output (site.net.wire (site.outsideEnd last)) role level
    oldLabels oldForward oldRoot oldFinish oldRole incoming requested
  exact ⟨result,replay requested result changed⟩
end

section
variable {B : Type} [FiniteNames B] {boundary : B → Bool} {root : B}

theorem GraphStep.cancellation_rootInputs {s : Schema} {g h : ActualNet B}
    (step : GraphStep s g h) (cancel : IsCancellation s)
    (flow : FlowBalance g.net boundary) (positive : boundary root=true)
    (inputs : RootInputs g.net root) : RootInputs h.net root := by
  cases step with
  | atSite kept site sourceIso targetIso =>
    exact targetIso.rootInputs (site.cancellation_rootInputs cancel (sourceIso.flowBalance flow)
      root positive (sourceIso.rootInputs inputs))

/-- This trace theorem covers only explicitly cancellation schemas. -/
theorem GraphTrace.cancellation_rootInputs {g h : ActualNet B} {schemas : List Schema}
    (trace : GraphTrace g h schemas) (cancels : ∀ s∈schemas,IsCancellation s)
    (flow : FlowBalance g.net boundary) (positive : boundary root=true)
    (inputs : RootInputs g.net root) : RootInputs h.net root := by
  induction trace with
  | iso same => exact same.rootInputs inputs
  | cons step tail ih =>
    obtain ⟨changedFlow⟩ := step.flowBalance flow
    exact ih (fun s member => cancels s (List.mem_cons_of_mem _ member)) changedFlow
      (step.cancellation_rootInputs (cancels _ (by simp)) flow positive inputs)
end
end Lamping.AG
