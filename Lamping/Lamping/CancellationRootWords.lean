import Lamping.Lamping.CancellationPathWords
import Lamping.Lamping.CancellationResidualReplay
import Lamping.Lamping.ReducedOutsideRoles
import Lamping.Lamping.MatchedControlInputs
import Lamping.Lamping.BackwardPathDeterminism
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- The removed nodes of a standard cancellation are controls, so every
actual incoming proper source endpoint is retained. -/
theorem PathSite.cancellation_source_incoming_kept (cancel : IsCancellation s)
    {root : B} {terminal : Endpoint site.net} {role : ProperRole} {level : Nat}
    (atPort : AtProperRole site.net root terminal role level) (incoming : role.incoming) :
    ∃ (node : K) (p : Port (kept node).sort),terminal=.inl ⟨.inl node,p⟩ := by
  cases atPort with
  | root => exact False.elim incoming
  | appFun => exact False.elim incoming
  | appArg => exact False.elim incoming
  | lamBody => exact False.elim incoming
  | appCtx node p level lab port
  | lamCtx node p level lab port
  | lamBind node p level lab port =>
    cases node with
    | inl node => exact ⟨node,p,rfl⟩
    | inr node => cases node <;> rename_i tag <;> cases tag <;> cases cancel <;> cases lab

private theorem kind_at_kept {old : List (Endpoint site.net)} {es : List (Endpoint site.reduce)}
    (node : K) (p : Port (kept node).sort)
    (oldEnd : old.getLast?=some (site.net.wire (.inl ⟨.inl node,p⟩)))
    (newEnd : es.getLast?=some (site.reduce.wire (.inl ⟨.inl node,p⟩))) :
    accessKind site.reduce es=accessKind site.net old := by
  simp only [accessKind,oldEnd,newEnd,Option.bind_some,Pairing.involutive]
  rfl

/-- Every actual old root access has an actual reduced access with the
same syntax word and observed endpoint kind. No Matches is assumed. -/
theorem PathSite.cancellation_root_access_forward (cancel : IsCancellation s)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (root : B) (positive : boundary root=true) (path : RootAccess site.net root) :
    ∃ reduced : RootAccess site.reduce root,
      accessWord site.reduce reduced.val=accessWord site.net path.val ∧
      accessKind site.reduce reduced.val=accessKind site.net path.val := by
  obtain ⟨terminal,role,level,finish,atPort,incoming⟩ := path.incoming_endpoint
  obtain ⟨node,p,same⟩ := site.cancellation_source_incoming_kept cancel atPort incoming
  rw [same] at finish
  let c := cutFragment site.net (pathPartition s V) site.closed
  let first : Endpoint c := .inr (.inl (.inl root))
  let last : Endpoint c := c.wire (.inl ⟨node,p⟩)
  obtain ⟨a,b,labels⟩ := path.property.1.1
  obtain ⟨es,newLabels,_residual,newRoot,newLast,word⟩ :=
    site.cancellation_source_word_contraction cancel labels path.property.1.2 path.property.2.2
      first last path.property.2.1 (by rw [←site.outsideEnd_wire]; exact finish)
  change es.head?=some (.inr (.inl root)) at newRoot
  have newEnd : es.getLast?=some (site.reduce.wire (.inl ⟨.inl node,p⟩)) := by
    simpa only [←plugLeft_wire c s.right.net (.inl ⟨node,p⟩)] using newLast
  have kind := kind_at_kept site node p finish newEnd
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  have newForward := newLabels.root_forward_of_flow newFlow root newRoot positive
  refine ⟨⟨es,⟨⟨⟨a,b,newLabels⟩,newForward⟩,newRoot,?_⟩⟩,word,kind⟩
  rw [kind]
  exact path.property.2.2

/-- Conversely, an actual reduced root access has an old root access with
the same word and endpoint kind. Contracting its chosen old ancestor back
with the original A/B and rooted terminal uniqueness locks the given path. -/
theorem PathSite.cancellation_root_access_backward (cancel : IsCancellation s)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (root : B) (positive : boundary root=true) (path : RootAccess site.reduce root) :
    ∃ old : RootAccess site.net root,
      accessWord site.net old.val=accessWord site.reduce path.val ∧
      accessKind site.net old.val=accessKind site.reduce path.val := by
  have empty : s.right.N → False := by cases cancel <;> exact Empty.elim
  obtain ⟨terminal,role,level,finish,atPort,incoming⟩ := path.incoming_endpoint
  obtain ⟨node,p,same⟩ := site.reduced_incoming_kept empty atPort incoming
  rw [same] at finish
  let c := cutFragment site.net (pathPartition s V) site.closed
  let r := s.right.net
  let first : Endpoint c := .inr (.inl (.inl root))
  let last : Endpoint c := c.wire (.inl ⟨node,p⟩)
  have actualLast : path.val.getLast?=some (AG.plugLeft c r last) := by
    rw [finish]
    exact congrArg some (plugLeft_wire c r (.inl ⟨node,p⟩))
  obtain ⟨a,b,labels⟩ := path.property.1.1
  obtain ⟨old,_residual,oldLabels,oldHead,oldLast,_replay⟩ :=
    site.cancellation_relabelling_ancestor cancel labels first last path.property.2.1 actualLast
  have oldRoot : old.head?=some (.inr (.inl root)) := oldHead
  have oldEnd : old.getLast?=some (site.net.wire (.inl ⟨.inl node,p⟩)) := by
    rw [←site.outsideEnd_wire] at oldLast
    exact oldLast
  have kind := kind_at_kept site node p oldEnd finish
  have oldTyped : ∃ k,accessKind site.net old=some k := by
    rw [←kind]
    exact path.property.2.2
  have oldForward := oldLabels.root_forward_of_flow flow root oldRoot positive
  obtain ⟨again,againLabels,_againResidual,againRoot,againLast,word⟩ :=
    site.cancellation_source_word_contraction cancel oldLabels oldForward oldTyped first last oldHead oldLast
  change again.head?=some (.inr (.inl root)) at againRoot
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  have againForward := againLabels.root_forward_of_flow newFlow root againRoot positive
  obtain ⟨samePath,_⟩ := Labelling.rooted_terminal_unique site.reduce againLabels againForward againRoot
    labels path.property.1.2 path.property.2.1 (againLast.trans actualLast.symm)
  rw [samePath] at word
  exact ⟨⟨old,⟨⟨⟨a,b,oldLabels⟩,oldForward⟩,oldRoot,oldTyped⟩⟩,word.symm,kind.symm⟩
end
end Lamping.AG

