import Lamping.Lamping.FragmentWriterSuffix
import Lamping.Lamping.ActionPendingLambdaWords
import Lamping.Lamping.InitialPathConstruction
import Lamping.Lamping.PlugPendingEndpoints
import Lamping.Lamping.ActionPrerequisiteCopyBranches
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

/-- Reflect the supplied pending prefix and append this SAME finite principal component.
The real RHS entry and original writer assignment fix the last auxiliary. -/
theorem PendingRhsBlock.fixed_principal_ancestor (action : IsAction s)
    (principal : SiteActionPrincipal site)
    {raw : List (PlugSegment cut s.right.net)} {input output result : Context}
    (pending : PendingRhsBlock cut s.right.net raw input output)
    (first : Endpoint cut) (head : raw.head?=some (.inl first)) (p : Aux s.active)
    (entry : site.outsideEnd (.inr (.inl (.inr pending.enter)))=.inl ⟨.inr (.inl ()),.inr p⟩)
    (tokens : accessTokens s.right.net pending.inside=[])
    (rule : Traversal s.low (.op s.active) (.inr p) (.inl ()) pending.middle result) :
    ∃ pre, Labelling site.net (pre++principal.edges) input result ∧
      pre.head?=some (site.outsideEnd first) ∧
      pre.getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)) ∧
      (pre++principal.edges).getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧
      accessWord site.reduce (raw.map (plugEnd _ _))=accessWord site.net (pre++principal.edges) := by
  obtain ⟨pre,labels,start,last,words⟩ := pending.action_canonical_word site action principal first head
  have wired : site.net.wire (site.outsideEnd pending.last)=
      site.outsideEnd (.inr (.inl (.inr pending.enter))) := by
    rw [site.outsideEnd_wire,pending.arrival]
  rw [entry] at wired
  have ending := congrArg site.net.wire.mate wired
  simp only [Pairing.involutive] at ending
  have actualLast := last.trans (congrArg some ending)
  have nonempty : principal.edges≠[] := by intro empty; have h:=principal.first; rw [empty] at h; cases h
  have routeLabels := transparent_route_labelling site.net principal.edges nonempty principal.transparent result
  have whole : Labelling site.net (pre++principal.edges) input result := labels.append_seam routeLabels (by
    intro e f atLast atFirst
    have sameE := Option.some.inj (atLast.symm.trans actualLast)
    have sameF := Option.some.inj (atFirst.symm.trans principal.first)
    subst e; subst f
    rw [Pairing.involutive]
    exact LabelledTurn.node (g:=site.net) (.inr (.inl ())) _ _ rule)
  refine ⟨pre,whole,start,actualLast,?_,?_⟩
  · rw [List.getLast?_append,principal.last,Option.some_or]
  · have preNonempty := labels.nonempty
    have appendWord : accessWord site.net (pre++principal.edges)=
        accessWord site.net pre++accessTokens site.net principal.edges := by
      cases pre with
      | nil => exact False.elim (preNonempty rfl)
      | cons e es => exact List.flatMap_append
    rw [appendWord,principal.tokens_empty site action,List.append_nil]
    simpa only [tokens,List.append_nil] using words
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.lam i j lt) V) site.closed

/-- An actual copied-lambda pending endpoint fixes the original incoming piece writer.
The original whole is identified by Matches, not by endpoint coincidence. -/
theorem SourceEdgeFragment.pending_lambda_writer
    {current : LTerm} {root : B} {edge : SourceEdge} {position : Path}
    (fragment : SourceEdgeFragment current site.net root edge position)
    {boundary : B → Bool} (matching : Matches site.net root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site)
    {raw : List (PlugSegment cut (Schema.fanAction .lam i j lt).right.net)} {input output : Context}
    (pending : PendingRhsBlock cut (Schema.fanAction .lam i j lt).right.net raw input output)
    (head : raw.head?=some (.inl (.inr (.inl (.inl root)))))
    (word : position=accessWord site.reduce (raw.map (plugEnd _ _))) (branch : Bool)
    (finish : pending.inside.getLast?=some ((fanRight .lam i j).wire (.inl ⟨.inl branch,.inl ()⟩))) :
    ∃ pre,fragment.segments=pre++principal.edges ∧
      pre.getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)) := by
  obtain ⟨same,shape,contexts⟩ := fanRight_lam_context_prefix i j branch pending.enter pending.inside
    pending.middle output pending.insideLabels pending.insideHead finish
  have entry : site.outsideEnd (.inr (.inl (.inr pending.enter)))=
      .inl ⟨.inr (.inl ()),.inr branch⟩ := by rw [same]; rfl
  have tokens : accessTokens (fanRight .lam i j) pending.inside=[] := by rw [shape]; rfl
  have rule : Traversal i (.op .fan) (.inr branch) (.inl ()) pending.middle
      (InitialOffsets.fanAt i branch output) := by
    rw [contexts]; exact .direct (InitialOffsets.Event.apply_rel (.fan i branch) output)
  obtain ⟨oldPre,labels,start,last,wholeLast,words⟩ := pending.fixed_principal_ancestor site
    (.fan .lam i j lt) principal (.inr (.inl (.inl root))) head branch entry tokens rule
  have rooted : (oldPre++principal.edges).head?=some (.inr (.inl root)) := by
    rw [List.head?_append,start,Option.some_or]; rfl
  have typed : accessKind site.net (oldPre++principal.edges)=some .lam := by
    simp only [accessKind,wholeLast,Option.bind_some,Pairing.involutive]; rfl
  let ancestor : RootAccess site.net root :=
    ⟨oldPre++principal.edges,⟨⟨⟨input,_,labels⟩,labels.root_forward_of_flow flow root rooted positive⟩,
      rooted,⟨.lam,typed⟩⟩⟩
  have accessEq : ancestor=fragment.access :=
    matching.accessWord_injective (words.symm.trans (word.symm.trans fragment.word.symm))
  have literal : oldPre++principal.edges=fragment.access.val := congrArg Subtype.val accessEq
  have originalLabels : Labelling site.net fragment.access.val input (InitialOffsets.fanAt i branch output) := by
    rw [←literal]; exact labels
  have terminal : fragment.toEndpoint=.inl ⟨.inr (.inr ()),.inl ()⟩ := by
    have accessLast : fragment.access.val.getLast?=fragment.segments.getLast? := by
      rw [fragment.literal,List.getLast?_append,fragment.finish,Option.some_or]
    have finishes := fragment.finish.symm.trans (accessLast.symm.trans (literal ▸ wholeLast))
    have wires := Option.some.inj finishes
    have ends := congrArg site.net.wire.mate wires
    simpa only [Pairing.involutive] using ends
  obtain ⟨pre,q,_pieceInput,_middle,split,_first,preLast,_piece,_before,_writer⟩ :=
    fragment.lambda_writer_suffix site (Or.inl rfl) rfl principal originalLabels terminal
  have totalSplit : oldPre++principal.edges=(fragment.before++pre)++principal.edges := by
    rw [literal,fragment.literal,split,List.append_assoc]
  have preEq : oldPre=fragment.before++pre := List.append_cancel_right totalSplit
  have exactLast : (fragment.before++pre).getLast?=pre.getLast? := by
    rw [List.getLast?_append,preLast,Option.some_or]
  have compare : (fragment.before++pre).getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)) := by
    rw [←preEq]; exact last
  have branchEq := site.writer_suffix_aux_unique principal (q:=q) (r:=branch)
    (left:=pre) (right:=pre) rfl preLast (exactLast.symm.trans compare)
  subst q
  exact ⟨pre,split,preLast⟩
/-- The real target access supplies its own pending decomposition. -/
theorem SourceEdgeFragment.target_lambda_writer
    {current : LTerm} {root : B} {edge : SourceEdge} {position : Path}
    (fragment : SourceEdgeFragment current site.net root edge position)
    {boundary : B → Bool} (matching : Matches site.net root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site) (target : RootAccess site.reduce root)
    (word : position=accessWord site.reduce target.val) (branch : Bool)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩))) :
    ∃ pre,fragment.segments=pre++principal.edges ∧
      pre.getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)) := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  obtain ⟨input,output,labels⟩ := target.property.1.1
  have actualHead : target.val.head?=some (AG.plugLeft cut (Schema.fanAction .lam i j lt).right.net first) :=
    target.property.2.1
  obtain ⟨pending,insideFinish⟩ := labels.pending_new_node cut (Schema.fanAction .lam i j lt).right.net
    first actualHead (.inl branch) (.inl ()) finish
  have rawHead : (target.val.map (plugEnd (cut).label (Schema.fanAction .lam i j lt).right.net.label).invFun).head?=
      some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd (cut).label (Schema.fanAction .lam i j lt).right.net.label).left_inv (.inl first))
  exact fragment.pending_lambda_writer site matching flow positive principal pending rawHead
    (by simpa only [plug_decomposition_flatten] using word) branch insideFinish
/-- Compare two given successful lambda prerequisite chains using source Joint.
Undefined endpoint status and the full action invariant remain separate obligations. -/
theorem PathSite.prerequisite_lambda_copy_branches
    {current : LTerm} {root : B} {boundary : B → Bool}
    (matching : Matches site.net root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site)
    (closed : Closed current.erase) (selection : OccurrenceFragmentSelection current site.net root)
    (joint : JointRepresentation closed selection)
    (leftLookup : current.subterm p=some (.lam leftStamp leftBody))
    (rightLookup : current.subterm q=some (.lam rightStamp rightBody))
    (leftChain : PrerequisiteChain current p left) (rightChain : PrerequisiteChain current q right)
    (iso : ChainIncidenceIsomorphic (chainSyntaxIncidence current closed left)
      (chainSyntaxIncidence current closed right))
    (leftTarget rightTarget : RootAccess site.reduce root)
    (leftWord : accessWord site.reduce leftTarget.val=p)
    (rightWord : accessWord site.reduce rightTarget.val=q)
    (leftBranch rightBranch : Bool)
    (leftFinish : leftTarget.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftBranch),.inl ()⟩)))
    (rightFinish : rightTarget.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightBranch),.inl ()⟩))) :
    leftBranch=rightBranch := by
  let leftPosition : Position current.erase := ⟨p,by rw [←LTerm.erase_subterm,leftLookup]; rfl⟩
  let rightPosition : Position current.erase := ⟨q,by rw [←LTerm.erase_subterm,rightLookup]; rfl⟩
  obtain ⟨leftPre,leftSplit,leftLast⟩ := (selection leftPosition).fragment.target_lambda_writer site
    matching flow positive principal leftTarget leftWord.symm leftBranch leftFinish
  obtain ⟨rightPre,rightSplit,rightLast⟩ := (selection rightPosition).fragment.target_lambda_writer site
    matching flow positive principal rightTarget rightWord.symm rightBranch rightFinish
  have leftHead : left.head?=some leftPosition.val := by
    rcases leftChain.lambda_cases leftLookup with ⟨_,_,_,_,_,same⟩|⟨_,_,_,_,_,same,_⟩ <;> rw [same] <;> rfl
  have rightHead : right.head?=some rightPosition.val := by
    rcases rightChain.lambda_cases rightLookup with ⟨_,_,_,_,_,same⟩|⟨_,_,_,_,_,same,_⟩ <;> rw [same] <;> rfl
  have physical := (joint.1 leftChain rightChain).mpr iso
  have heads := congrArg List.head? physical
  rw [canonical_chain_head selection leftChain leftPosition leftHead,
    canonical_chain_head selection rightChain rightPosition rightHead] at heads
  have same := Option.some.inj heads
  exact site.writer_suffix_aux_unique principal (leftSplit.symm.trans (same.trans rightSplit)) leftLast rightLast
end
end Lamping.AG