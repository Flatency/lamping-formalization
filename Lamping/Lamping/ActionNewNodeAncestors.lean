import Lamping.Lamping.ActionPendingAncestors
import Lamping.Lamping.PlugPendingEndpoints
namespace Lamping.AG
open Graph
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {f : Op} {i j : Nat} {lt : i<j}

/-- Direct actual-root interface: no pending block or partial-path transport
witness is supplied. The source endpoint context may differ at low levels. -/
theorem PathSite.fan_new_aux_ancestor
    (site : PathSite (.fanAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (root : B) (positive : boundary root=true)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output) (rooted : es.head?=some (.inr (.inl root)))
    (branch : Bool) (q : Aux f)
    (finish : es.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inr q⟩))) :
    ∃ old oldContext,Labelling site.net old input oldContext ∧Forward site.net old ∧
      old.head?=some (.inr (.inl root)) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)) ∧oldContext.tail j=output.tail j := by
  let first : Endpoint (cutFragment site.net (pathPartition (.fanAction f i j lt) V) site.closed) :=
    .inr (.inl (.inl root))
  have head : es.head?=some (AG.plugLeft _ _ first) := rooted
  obtain ⟨pending,insideLast⟩ := labels.pending_new_node _ _ first head (.inl branch) (.inr q) finish
  have rawHead : (es.map (plugEnd _ _).invFun).head?=some (.inl first) := by
    rw [List.head?_map,head]
    exact congrArg some ((plugEnd _ _).left_inv (.inl first))
  obtain ⟨old,oldLabels,oldHead,oldLast,tails⟩ := site.fan_pending_aux_ancestor pending first rawHead branch q insideLast
  have oldRoot : old.head?=some (.inr (.inl root)) := oldHead
  exact ⟨old,pending.middle,oldLabels,oldLabels.root_forward_of_flow flow root oldRoot positive,oldRoot,oldLast,tails⟩

theorem PathSite.cro_new_aux_ancestor
    (site : PathSite (.croAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (root : B) (positive : boundary root=true)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output) (rooted : es.head?=some (.inr (.inl root)))
    (q : Aux f) (finish : es.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inr q⟩))) :
    ∃ old oldContext,Labelling site.net old input oldContext ∧Forward site.net old ∧
      old.head?=some (.inr (.inl root)) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)) ∧oldContext.tail j=output.tail (j-1) := by
  let first : Endpoint (cutFragment site.net (pathPartition (.croAction f i j lt) V) site.closed) :=
    .inr (.inl (.inl root))
  have head : es.head?=some (AG.plugLeft _ _ first) := rooted
  obtain ⟨pending,insideLast⟩ := labels.pending_new_node _ _ first head (.inl ()) (.inr q) finish
  have rawHead : (es.map (plugEnd _ _).invFun).head?=some (.inl first) := by
    rw [List.head?_map,head]
    exact congrArg some ((plugEnd _ _).left_inv (.inl first))
  obtain ⟨old,oldLabels,oldHead,oldLast,tails⟩ := site.cro_pending_aux_ancestor pending first rawHead q insideLast
  have oldRoot : old.head?=some (.inr (.inl root)) := oldHead
  exact ⟨old,pending.middle,oldLabels,oldLabels.root_forward_of_flow flow root oldRoot positive,oldRoot,oldLast,tails⟩

theorem PathSite.bra_new_aux_ancestor
    (site : PathSite (.braAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (root : B) (positive : boundary root=true)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output) (rooted : es.head?=some (.inr (.inl root)))
    (q : Aux f) (finish : es.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inr q⟩))) :
    ∃ old oldContext,Labelling site.net old input oldContext ∧Forward site.net old ∧
      old.head?=some (.inr (.inl root)) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)) ∧oldContext.tail j=output.tail (j+1) := by
  let first : Endpoint (cutFragment site.net (pathPartition (.braAction f i j lt) V) site.closed) :=
    .inr (.inl (.inl root))
  have head : es.head?=some (AG.plugLeft _ _ first) := rooted
  obtain ⟨pending,insideLast⟩ := labels.pending_new_node _ _ first head (.inl ()) (.inr q) finish
  have rawHead : (es.map (plugEnd _ _).invFun).head?=some (.inl first) := by
    rw [List.head?_map,head]
    exact congrArg some ((plugEnd _ _).left_inv (.inl first))
  obtain ⟨old,oldLabels,oldHead,oldLast,tails⟩ := site.bra_pending_aux_ancestor pending first rawHead q insideLast
  have oldRoot : old.head?=some (.inr (.inl root)) := oldHead
  exact ⟨old,pending.middle,oldLabels,oldLabels.root_forward_of_flow flow root oldRoot positive,oldRoot,oldLast,tails⟩
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}

theorem PathSite.fan_new_lam_context_ancestor
    (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (root : B) (positive : boundary root=true)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output) (rooted : es.head?=some (.inr (.inl root)))
    (branch : Bool) (finish : es.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩))) :
    ∃ old,Labelling site.net old input (InitialOffsets.fanAt i branch output) ∧Forward site.net old ∧
      old.head?=some (.inr (.inl root)) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧
      (InitialOffsets.fanAt i branch output).tail j=output.tail j := by
  let first : Endpoint (cutFragment site.net (pathPartition (.fanAction .lam i j lt) V) site.closed) :=
    .inr (.inl (.inl root))
  have head : es.head?=some (AG.plugLeft _ _ first) := rooted
  obtain ⟨pending,insideLast⟩ := labels.pending_new_node _ _ first head (.inl branch) (.inl ()) finish
  have rawHead : (es.map (plugEnd _ _).invFun).head?=some (.inl first) := by
    rw [List.head?_map,head]
    exact congrArg some ((plugEnd _ _).left_inv (.inl first))
  obtain ⟨old,oldLabels,oldHead,oldLast,tails⟩ := site.fan_pending_lam_ancestor pending first rawHead branch insideLast
  have oldRoot : old.head?=some (.inr (.inl root)) := oldHead
  exact ⟨old,oldLabels,oldLabels.root_forward_of_flow flow root oldRoot positive,oldRoot,oldLast,tails⟩

theorem PathSite.cro_new_lam_context_ancestor
    (site : PathSite (.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (root : B) (positive : boundary root=true)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output) (rooted : es.head?=some (.inr (.inl root)))
    (finish : es.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩))) :
    ∃ old,Labelling site.net old input (InitialOffsets.croAt i output) ∧Forward site.net old ∧
      old.head?=some (.inr (.inl root)) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧
      (InitialOffsets.croAt i output).tail j=output.tail (j-1) := by
  let first : Endpoint (cutFragment site.net (pathPartition (.croAction .lam i j lt) V) site.closed) :=
    .inr (.inl (.inl root))
  have head : es.head?=some (AG.plugLeft _ _ first) := rooted
  obtain ⟨pending,insideLast⟩ := labels.pending_new_node _ _ first head (.inl ()) (.inl ()) finish
  have rawHead : (es.map (plugEnd _ _).invFun).head?=some (.inl first) := by
    rw [List.head?_map,head]
    exact congrArg some ((plugEnd _ _).left_inv (.inl first))
  obtain ⟨old,oldLabels,oldHead,oldLast,tails⟩ := site.cro_pending_lam_ancestor pending first rawHead insideLast
  have oldRoot : old.head?=some (.inr (.inl root)) := oldHead
  exact ⟨old,oldLabels,oldLabels.root_forward_of_flow flow root oldRoot positive,oldRoot,oldLast,tails⟩

theorem PathSite.bra_new_lam_context_ancestor
    (site : PathSite (.braAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (root : B) (positive : boundary root=true)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output) (rooted : es.head?=some (.inr (.inl root)))
    (finish : es.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩))) :
    ∃ old,Labelling site.net old input (InitialOffsets.braAt i output) ∧Forward site.net old ∧
      old.head?=some (.inr (.inl root)) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧
      (InitialOffsets.braAt i output).tail j=output.tail (j+1) := by
  let first : Endpoint (cutFragment site.net (pathPartition (.braAction .lam i j lt) V) site.closed) :=
    .inr (.inl (.inl root))
  have head : es.head?=some (AG.plugLeft _ _ first) := rooted
  obtain ⟨pending,insideLast⟩ := labels.pending_new_node _ _ first head (.inl ()) (.inl ()) finish
  have rawHead : (es.map (plugEnd _ _).invFun).head?=some (.inl first) := by
    rw [List.head?_map,head]
    exact congrArg some ((plugEnd _ _).left_inv (.inl first))
  obtain ⟨old,oldLabels,oldHead,oldLast,tails⟩ := site.bra_pending_lam_ancestor pending first rawHead insideLast
  have oldRoot : old.head?=some (.inr (.inl root)) := oldHead
  exact ⟨old,oldLabels,oldLabels.root_forward_of_flow flow root oldRoot positive,oldRoot,oldLast,tails⟩
end
end Lamping.AG
