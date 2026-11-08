import Lamping.Lamping.ActionParentFunctionBranches
import Lamping.Lamping.ActionPendingWords
import Lamping.Lamping.PlugPendingEndpoints
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.app i j lt) V) site.closed

/-- A real pending RHS reader is compared with the original function
piece at ONE specified original assignment. No path totality is assumed. -/
theorem SourceEdgeFragment.fan_pending_branch_at_reference
    {current : LTerm} {root : B} {edge : SourceEdge} {position : Path}
    (fragment : SourceEdgeFragment current site.net root edge position)
    (first : fragment.fromEndpoint=.inl ⟨.inr (.inr ()),.inl ()⟩)
    {raw : List (PlugSegment cut (Schema.fanAction .app i j lt).right.net)} {input output : Context}
    (pending : PendingRhsBlock cut (Schema.fanAction .app i j lt).right.net raw input output)
    {oldInput oldOutput : Context} (whole : Labelling site.net fragment.access.val oldInput oldOutput)
    (before : Labelling site.net (fragment.before++[fragment.fromEndpoint]) oldInput pending.middle)
    (branch : Bool)
    (finish : pending.inside.getLast?=some ((fanRight .app i j).wire (.inl ⟨.inl branch,appCtx⟩))) :
    ∀ a b,Labelling site.net fragment.segments a b →
      ∃ middle,Traversal i (.op .fan) (.inl ()) (.inr branch) a middle := by
  obtain ⟨q,uniform,identify⟩ := fragment.function_branch_at_prefix site (Or.inl rfl) first
  obtain ⟨_entry,_inside,reader⟩ := fanRight_copied_aux_prefix .app i j branch false
    pending.enter pending.inside pending.middle output pending.insideLabels pending.insideHead finish
  have same := identify whole before reader
  subst q
  exact uniform
theorem SourceEdgeFragment.fan_pending_function_branch
    {current term : LTerm} {root : B} {edge : SourceEdge} {position : Path}
    (fragment : SourceEdgeFragment current site.net root edge position)
    {boundary : B → Bool} (matching : Matches site.net root current.erase)
    (inputs : RootInputs site.net root) (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (role : SourceDeparture term .fn edge.fromPort) (parent : RootAccess site.net root)
    (word : position=accessWord site.net parent.val++[.fn])
    {raw : List (PlugSegment cut (Schema.fanAction .app i j lt).right.net)} {input output : Context}
    (pending : PendingRhsBlock cut (Schema.fanAction .app i j lt).right.net raw input output)
    (head : raw.head?=some (.inl (.inr (.inl (.inl root)))))
    (parentWord : accessWord site.net parent.val=
      accessWord site.reduce (raw.map (plugEnd (cut).label (Schema.fanAction .app i j lt).right.net.label)))
    (branch : Bool)
    (finish : pending.inside.getLast?=some ((fanRight .app i j).wire (.inl ⟨.inl branch,appCtx⟩))) :
    ∀ a b,Labelling site.net fragment.segments a b →
      ∃ middle,Traversal i (.op .fan) (.inl ()) (.inr branch) a middle := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  obtain ⟨old,labels,rooted,last,words,_tails⟩ :=
    site.fan_pending_aux_ancestor_word pending first head branch false finish
  have oldRoot : old.head?=some (.inr (.inl root)) := rooted
  have typed : accessKind site.net old=some .app := by
    simp only [accessKind,last,Option.bind_some,Pairing.involutive]
    rfl
  let oldParent : RootAccess site.net root :=
    ⟨old,⟨⟨⟨input,pending.middle,labels⟩,labels.root_forward_of_flow flow root oldRoot positive⟩,
      oldRoot,⟨.app,typed⟩⟩⟩
  have same : oldParent=parent := matching.accessWord_injective (words.symm.trans parentWord.symm)
  have literal : old=parent.val := congrArg Subtype.val same
  rw [literal] at labels last
  obtain ⟨chosen,uniform,onParent⟩ := fragment.parent_function_control_branch site matching inputs
    (Or.inl rfl) rfl role parent appCtx HEq.rfl word last
  obtain ⟨middle,reader⟩ := onParent input pending.middle labels
  obtain ⟨_entry,_inside,actualReader⟩ := fanRight_copied_aux_prefix .app i j branch false
    pending.enter pending.inside pending.middle output pending.insideLabels pending.insideHead finish
  have sameBranch : chosen=branch := reader.control_auxiliary_unique (Or.inl rfl) actualReader
  subst chosen
  exact uniform

theorem SourceEdgeFragment.fan_target_app_function_branch
    {current term : LTerm} {root : B} {edge : SourceEdge} {position : Path}
    (fragment : SourceEdgeFragment current site.net root edge position)
    {boundary : B → Bool} (matching : Matches site.net root current.erase)
    (inputs : RootInputs site.net root) (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (role : SourceDeparture term .fn edge.fromPort) (parent : RootAccess site.net root)
    (word : position=accessWord site.net parent.val++[.fn])
    (target : RootAccess site.reduce root)
    (sameWord : accessWord site.net parent.val=accessWord site.reduce target.val)
    (branch : Bool)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),appCtx⟩))) :
    ∀ a b,Labelling site.net fragment.segments a b →
      ∃ middle,Traversal i (.op .fan) (.inl ()) (.inr branch) a middle := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  obtain ⟨input,output,labels⟩ := target.property.1.1
  have actualHead : target.val.head?=some (AG.plugLeft cut (Schema.fanAction .app i j lt).right.net first) :=
    target.property.2.1
  obtain ⟨pending,insideFinish⟩ := labels.pending_new_node cut (Schema.fanAction .app i j lt).right.net
    first actualHead (.inl branch) appCtx finish
  have rawHead : (target.val.map (plugEnd (cut).label (Schema.fanAction .app i j lt).right.net.label).invFun).head?=
      some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd (cut).label (Schema.fanAction .app i j lt).right.net.label).left_inv (.inl first))
  apply fragment.fan_pending_function_branch site matching inputs flow positive role parent word
    pending rawHead (by simpa only [plug_decomposition_flatten] using sameWord) branch insideFinish
end
end Lamping.AG