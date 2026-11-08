import Lamping.Lamping.ActionAncestor
import Lamping.Lamping.PlugPendingBlocks
import Lamping.Lamping.SourceContextPrefixes
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

theorem PathSite.pending_outside_ancestor (action : IsAction s)
    {raw : List (PlugSegment (cutFragment site.net (pathPartition s V) site.closed) s.right.net)}
    {input output : Context}
    (pending : PendingRhsBlock (cutFragment site.net (pathPartition s V) site.closed) s.right.net raw input output)
    (first : Endpoint (cutFragment site.net (pathPartition s V) site.closed))
    (head : raw.head?=some (.inl first)) :
    ∃ old,LocalBlockResidual (cutFragment site.net (pathPartition s V) site.closed) s.right.net
      site.net site.outsideEnd pending.pre old ∧Labelling site.net old input pending.middle ∧
      old.head?=some (site.outsideEnd first) ∧old.getLast?=some (site.outsideEnd pending.last) := by
  exact pending.prefixPath.lift_routes _ _ site.net site.outsideEnd site.outsideEnd_wire
    (fun turn => turn.outsideEnd site) (fun entry exit a b path => site.action_local_route action entry exit a b path)
    first pending.last (pending.prefixHead.trans head) pending.prefixLast

private theorem outside_aux_end
    (e : Endpoint (cutFragment site.net (pathPartition s V) site.closed)) (entry : s.Frontier)
    (arrival : (cutFragment site.net (pathPartition s V) site.closed).wire e=.inr (.inl (.inr entry))) :
    site.outsideEnd e=site.net.wire (site.outsideEnd (.inr (.inl (.inr entry)))) := by
  have wired : site.net.wire (site.outsideEnd e)=site.outsideEnd (.inr (.inl (.inr entry))) := by
    rw [site.outsideEnd_wire,arrival]
  have same := congrArg site.net.wire.mate wired
  simpa only [Pairing.involutive] using same

private theorem join_at_last {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {xs ys : List (Endpoint g)} {a middle b : Context}
    (left : Labelling g xs a middle) (right : Labelling g ys middle b)
    (e first last : Endpoint g) (leftHead : xs.head?=some first) (leftLast : xs.getLast?=some e)
    (rightHead : ys.head?=some e) (rightLast : ys.getLast?=some last) :
    ∃ joined,Labelling g joined a b ∧joined.head?=some first ∧joined.getLast?=some last := by
  obtain ⟨pre,leftSplit⟩ := List.getLast?_eq_some_iff.mp leftLast
  obtain ⟨post,rightSplit⟩ := List.head?_eq_some_iff.mp rightHead
  rw [leftSplit] at left
  rw [rightSplit] at right
  refine ⟨pre++e::post,left.join right,?_,?_⟩
  · cases pre with
    | nil => simpa only [leftSplit,List.nil_append,List.head?_cons] using leftHead
    | cons x pre => simpa only [leftSplit,List.cons_append,List.head?_cons] using leftHead
  · rw [List.getLast?_append]
    have lastEq : (e::post).getLast?=some last := by simpa only [rightSplit] using rightLast
    rw [lastEq,Option.some_or]

private theorem pending_join (action : IsAction s)
    {raw : List (PlugSegment (cutFragment site.net (pathPartition s V) site.closed) s.right.net)}
    {input output result : Context}
    (pending : PendingRhsBlock (cutFragment site.net (pathPartition s V) site.closed) s.right.net raw input output)
    (first : Endpoint (cutFragment site.net (pathPartition s V) site.closed))
    (head : raw.head?=some (.inl first)) (localEdges : List (Endpoint site.net)) (target : Endpoint site.net)
    (localHead : localEdges.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr pending.enter))))))
    (localLast : localEdges.getLast?=some target)
    (localLabels : Labelling site.net localEdges pending.middle result) :
    ∃ old,Labelling site.net old input result ∧
      old.head?=some (site.outsideEnd first) ∧old.getLast?=some target := by
  obtain ⟨old,_,labels,start,last⟩ := site.pending_outside_ancestor action pending first head
  have same := outside_aux_end site pending.last pending.enter pending.arrival
  rw [←same] at localHead
  exact join_at_last labels localLabels _ _ _ start last localHead localLast
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {f : Op} {i j : Nat} {lt : i<j}

/-- Actual whole-prefix ancestor for a copied auxiliary terminal. Its old
terminal context is the actual last outside context, not the target context;
the high typed tails are related explicitly. -/
theorem PathSite.fan_pending_aux_ancestor
    (site : PathSite (.fanAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    {raw : List (PlugSegment (cutFragment site.net (pathPartition (.fanAction f i j lt) V) site.closed)
      (Schema.fanAction f i j lt).right.net)} {input output : Context}
    (pending : PendingRhsBlock (cutFragment site.net (pathPartition (.fanAction f i j lt) V) site.closed)
      (Schema.fanAction f i j lt).right.net raw input output)
    (first : Endpoint (cutFragment site.net (pathPartition (.fanAction f i j lt) V) site.closed))
    (head : raw.head?=some (.inl first)) (branch : Bool) (q : Aux f)
    (finish : pending.inside.getLast?=some ((fanRight f i j).wire (.inl ⟨.inl branch,.inr q⟩))) :
    ∃ old,Labelling site.net old input pending.middle ∧
      old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)) ∧
      pending.middle.tail j=output.tail j := by
  obtain ⟨same,_,tails⟩ := site.fan_aux_context_ancestor branch q pending.enter pending.inside
    pending.middle output pending.insideLabels pending.insideHead finish
  obtain ⟨old,_,labels,start,last⟩ := site.pending_outside_ancestor (.fan f i j lt) pending first head
  have ending := outside_aux_end site pending.last pending.enter pending.arrival
  rw [same] at ending
  rw [ending] at last
  exact ⟨old,labels,start,last,tails⟩

theorem PathSite.cro_pending_aux_ancestor
    (site : PathSite (.croAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    {raw : List (PlugSegment (cutFragment site.net (pathPartition (.croAction f i j lt) V) site.closed)
      (Schema.croAction f i j lt).right.net)} {input output : Context}
    (pending : PendingRhsBlock (cutFragment site.net (pathPartition (.croAction f i j lt) V) site.closed)
      (Schema.croAction f i j lt).right.net raw input output)
    (first : Endpoint (cutFragment site.net (pathPartition (.croAction f i j lt) V) site.closed))
    (head : raw.head?=some (.inl first)) (q : Aux f)
    (finish : pending.inside.getLast?=some ((unaryRightCore .cro f (Bij.refl _) i (j-1)).wire (.inl ⟨.inl (),.inr q⟩))) :
    ∃ old,Labelling site.net old input pending.middle ∧
      old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)) ∧
      pending.middle.tail j=output.tail (j-1) := by
  obtain ⟨same,_,tails⟩ := site.cro_aux_context_ancestor q pending.enter pending.inside
    pending.middle output pending.insideLabels pending.insideHead finish
  obtain ⟨old,_,labels,start,last⟩ := site.pending_outside_ancestor (.cro f i j lt) pending first head
  have ending := outside_aux_end site pending.last pending.enter pending.arrival
  rw [same] at ending
  rw [ending] at last
  exact ⟨old,labels,start,last,tails⟩

theorem PathSite.bra_pending_aux_ancestor
    (site : PathSite (.braAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    {raw : List (PlugSegment (cutFragment site.net (pathPartition (.braAction f i j lt) V) site.closed)
      (Schema.braAction f i j lt).right.net)} {input output : Context}
    (pending : PendingRhsBlock (cutFragment site.net (pathPartition (.braAction f i j lt) V) site.closed)
      (Schema.braAction f i j lt).right.net raw input output)
    (first : Endpoint (cutFragment site.net (pathPartition (.braAction f i j lt) V) site.closed))
    (head : raw.head?=some (.inl first)) (q : Aux f)
    (finish : pending.inside.getLast?=some ((unaryRightCore .bra f (Bij.refl _) i (j+1)).wire (.inl ⟨.inl (),.inr q⟩))) :
    ∃ old,Labelling site.net old input pending.middle ∧
      old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)) ∧
      pending.middle.tail j=output.tail (j+1) := by
  obtain ⟨same,_,tails⟩ := site.bra_aux_context_ancestor q pending.enter pending.inside
    pending.middle output pending.insideLabels pending.insideHead finish
  obtain ⟨old,_,labels,start,last⟩ := site.pending_outside_ancestor (.bra f i j lt) pending first head
  have ending := outside_aux_end site pending.last pending.enter pending.arrival
  rw [same] at ending
  rw [ending] at last
  exact ⟨old,labels,start,last,tails⟩
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}

theorem PathSite.fan_pending_lam_ancestor
    (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {raw : List (PlugSegment (cutFragment site.net (pathPartition (.fanAction .lam i j lt) V) site.closed)
      (Schema.fanAction .lam i j lt).right.net)} {input output : Context}
    (pending : PendingRhsBlock (cutFragment site.net (pathPartition (.fanAction .lam i j lt) V) site.closed)
      (Schema.fanAction .lam i j lt).right.net raw input output)
    (first : Endpoint (cutFragment site.net (pathPartition (.fanAction .lam i j lt) V) site.closed))
    (head : raw.head?=some (.inl first)) (branch : Bool)
    (finish : pending.inside.getLast?=some ((fanRight .lam i j).wire (.inl ⟨.inl branch,.inl ()⟩))) :
    ∃ old,Labelling site.net old input (InitialOffsets.fanAt i branch output) ∧
      old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧
      (InitialOffsets.fanAt i branch output).tail j=output.tail j := by
  obtain ⟨same,localEdges,start,last,labels,tails⟩ := site.fan_lam_context_ancestor branch pending.enter
    pending.inside pending.middle output pending.insideLabels pending.insideHead finish
  have actualHead : localEdges.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr pending.enter))))) := by
    rw [same]
    exact start
  obtain ⟨old,oldLabels,oldStart,oldLast⟩ := pending_join site (.fan .lam i j lt) pending first head
    localEdges _ actualHead last labels
  exact ⟨old,oldLabels,oldStart,oldLast,tails⟩

theorem PathSite.cro_pending_lam_ancestor
    (site : PathSite (.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {raw : List (PlugSegment (cutFragment site.net (pathPartition (.croAction .lam i j lt) V) site.closed)
      (Schema.croAction .lam i j lt).right.net)} {input output : Context}
    (pending : PendingRhsBlock (cutFragment site.net (pathPartition (.croAction .lam i j lt) V) site.closed)
      (Schema.croAction .lam i j lt).right.net raw input output)
    (first : Endpoint (cutFragment site.net (pathPartition (.croAction .lam i j lt) V) site.closed))
    (head : raw.head?=some (.inl first))
    (finish : pending.inside.getLast?=some ((unaryRightCore .cro .lam (Bij.refl _) i (j-1)).wire (.inl ⟨.inl (),.inl ()⟩))) :
    ∃ old,Labelling site.net old input (InitialOffsets.croAt i output) ∧
      old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧
      (InitialOffsets.croAt i output).tail j=output.tail (j-1) := by
  obtain ⟨same,localEdges,start,last,labels,tails⟩ := site.cro_lam_context_ancestor pending.enter
    pending.inside pending.middle output pending.insideLabels pending.insideHead finish
  have actualHead : localEdges.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr pending.enter))))) := by
    rw [same]
    exact start
  obtain ⟨old,oldLabels,oldStart,oldLast⟩ := pending_join site (.cro .lam i j lt) pending first head
    localEdges _ actualHead last labels
  exact ⟨old,oldLabels,oldStart,oldLast,tails⟩

theorem PathSite.bra_pending_lam_ancestor
    (site : PathSite (.braAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {raw : List (PlugSegment (cutFragment site.net (pathPartition (.braAction .lam i j lt) V) site.closed)
      (Schema.braAction .lam i j lt).right.net)} {input output : Context}
    (pending : PendingRhsBlock (cutFragment site.net (pathPartition (.braAction .lam i j lt) V) site.closed)
      (Schema.braAction .lam i j lt).right.net raw input output)
    (first : Endpoint (cutFragment site.net (pathPartition (.braAction .lam i j lt) V) site.closed))
    (head : raw.head?=some (.inl first))
    (finish : pending.inside.getLast?=some ((unaryRightCore .bra .lam (Bij.refl _) i (j+1)).wire (.inl ⟨.inl (),.inl ()⟩))) :
    ∃ old,Labelling site.net old input (InitialOffsets.braAt i output) ∧
      old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧
      (InitialOffsets.braAt i output).tail j=output.tail (j+1) := by
  obtain ⟨same,localEdges,start,last,labels,tails⟩ := site.bra_lam_context_ancestor pending.enter
    pending.inside pending.middle output pending.insideLabels pending.insideHead finish
  have actualHead : localEdges.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr pending.enter))))) := by
    rw [same]
    exact start
  obtain ⟨old,oldLabels,oldStart,oldLast⟩ := pending_join site (.bra .lam i j lt) pending first head
    localEdges _ actualHead last labels
  exact ⟨old,oldLabels,oldStart,oldLast,tails⟩
end
end Lamping.AG
