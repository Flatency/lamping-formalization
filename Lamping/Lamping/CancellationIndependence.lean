import Lamping.Lamping.CancellationResidualReplay
import Lamping.Lamping.ReducedOutsideProperRoles
import Lamping.Lamping.NetIsoInvariantTransport
import Lamping.Lamping.InitialFullIndependence
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- All three actual cancellations preserve FULL Independence, for arbitrary
proper outgoing sources as well as the root. The same-assignment ancestor has
the same retained source/target roles and indices; its one chosen literal
residual replays both arbitrary source replacements and synchronized tails. -/
theorem PathSite.cancellation_independence (cancel : IsCancellation s)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (root : B) (positive : boundary root=true) (indep : Independence site.net root) :
    Independence site.reduce root := by
  intro es e f sr tr m n a b first finish source outgoing target incoming _forward labels
  have empty : s.right.N → False := by cases cancel <;> exact Empty.elim
  let c := cutFragment site.net (pathPartition s V) site.closed
  let r := s.right.net
  obtain ⟨sourceEnd,sourceEq⟩ := site.reduced_proper_outside empty source
  obtain ⟨targetEnd,targetEq⟩ := site.reduced_proper_outside empty target
  have oldSource : AtProperRole site.net root (site.outsideEnd sourceEnd) sr m :=
    site.reduced_outside_proper_role root sourceEnd sr m (by rw [←sourceEq]; exact source)
  have oldTarget : AtProperRole site.net root (site.outsideEnd targetEnd) tr n :=
    site.reduced_outside_proper_role root targetEnd tr n (by rw [←targetEq]; exact target)
  have targetWire : site.reduce.wire f=AG.plugLeft c r (c.wire targetEnd) := by
    rw [targetEq]
    exact plugLeft_wire c r targetEnd
  obtain ⟨old,_residual,oldLabels,oldHead,oldLast,replay⟩ :=
    site.cancellation_relabelling_ancestor cancel labels sourceEnd (c.wire targetEnd)
      (first.trans (congrArg some sourceEq)) (finish.trans (congrArg some targetWire))
  have oldFinish : old.getLast?=some (site.net.wire (site.outsideEnd targetEnd)) := by
    rw [←site.outsideEnd_wire] at oldLast
    exact oldLast
  have oldForward : Forward site.net old := by
    apply oldLabels.forward_of_flow flow
    intro here head
    have same := Option.some.inj (head.symm.trans oldHead)
    subst here
    exact oldSource.outgoing_flow outgoing flow.nodes boundary flow.vertices positive
  obtain ⟨replaceInputs,width,lower,strict,fixed,sync⟩ :=
    indep old (site.outsideEnd sourceEnd) (site.outsideEnd targetEnd) sr tr m n a b
      oldHead oldFinish oldSource outgoing oldTarget incoming oldForward oldLabels
  refine ⟨?_,width,lower,strict,fixed,?_⟩
  · intro requested
    obtain ⟨result,changed⟩ := replaceInputs requested
    exact ⟨result,replay _ _ changed⟩
  · intro tail
    exact replay _ _ (sync tail)
end

section
variable {B : Type} [FiniteNames B] {boundary : B → Bool} {root : B}

theorem GraphStep.cancellation_independence {s : Schema} {g h : ActualNet B}
    (step : GraphStep s g h) (cancel : IsCancellation s)
    (flow : FlowBalance g.net boundary) (positive : boundary root=true)
    (old : Independence g.net root) : Independence h.net root := by
  cases step with
  | atSite kept site sourceIso targetIso =>
    exact targetIso.independence (site.cancellation_independence cancel
      (sourceIso.flowBalance flow) root positive (sourceIso.independence old))

/-- This finite-trace corollary is deliberately restricted to the actual
three cancellation schemas; beta and action preservation are not assumed. -/
theorem GraphTrace.cancellation_independence {g h : ActualNet B} {schemas : List Schema}
    (trace : GraphTrace g h schemas) (cancels : ∀ s∈schemas,IsCancellation s)
    (flow : FlowBalance g.net boundary) (positive : boundary root=true)
    (old : Independence g.net root) : Independence h.net root := by
  induction trace with
  | iso same => exact same.independence old
  | cons step tail ih =>
    obtain ⟨changedFlow⟩ := step.flowBalance flow
    exact ih (fun s mem => cancels s (List.mem_cons_of_mem _ mem)) changedFlow
      (step.cancellation_independence (cancels _ (by simp)) flow positive old)
end

/-- Actual closed initial translations retain full Independence along every
finite cancellation-only trace. This is not the all-schema SND theorem. -/
theorem initial_cancellation_trace_independence (t : Lambda.Term) (closed : Lambda.Closed t)
    (target : ActualNet (Boundary t)) (schemas : List Schema)
    (trace : GraphTrace (ActualNet.initial t) target schemas)
    (cancels : ∀ s∈schemas,IsCancellation s) : Independence target.net (.inl ()) := by
  obtain ⟨flow⟩ := encode_flowBalance t 0
  exact trace.cancellation_independence cancels flow rfl (encode_closed_independence t closed 0)
end Lamping.AG

