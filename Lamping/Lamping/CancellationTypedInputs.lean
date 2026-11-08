import Lamping.Lamping.CancellationResidualReplay
import Lamping.Lamping.ReducedOutsideRoles
import Lamping.Lamping.FlowRootPaths
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- Actual cancellation preserves the root-input existence component for
every supplied typed ordinary reduced path. Retained endpoint metadata and
the constant-block ancestor are derived from the physical rewrite itself. -/
theorem PathSite.cancellation_typed_root_inputs (cancel : IsCancellation s)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (root : B) (positive : boundary root=true) (indep : Independence site.net root)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output)
    (rooted : es.head?=some (.inr (.inl root)))
    (terminal : Endpoint site.reduce) (role : ProperRole) (level : Nat)
    (finish : es.getLast?=some (site.reduce.wire terminal))
    (atTerminal : AtProperRole site.reduce root terminal role level) (incoming : role.incoming) :
    ∀ requested : Context,∃ result,Labelling site.reduce es requested result := by
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
  obtain ⟨allInputs,_⟩ := indep old (.inr (.inl root)) (site.net.wire (site.outsideEnd last)) .root role
    0 level input output oldRoot oldFinish (.root) trivial oldRole incoming oldForward oldLabels
  intro requested
  obtain ⟨result,changed⟩ := allInputs requested
  exact ⟨result,replay requested result (by simpa only [Context.replace_zero] using changed)⟩
end
end Lamping.AG
