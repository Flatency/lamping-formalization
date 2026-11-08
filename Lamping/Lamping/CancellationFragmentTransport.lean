import Lamping.Lamping.CancellationResidualTypedCut
import Lamping.Lamping.CancellationCanonicalComparison
import Lamping.Lamping.ChainFragmentUniqueness
import Lamping.Lamping.MatchingSharedSyntaxEvaluation
import Lamping.Lamping.CancellationRootWords
import Lamping.Lamping.CancellationCanonicalResidual
import Lamping.Lamping.ChainRepresentation
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

theorem SourceEdgeFragment.fragment_kind
    (fragment : SourceEdgeFragment current g root edge position) :
    accessKind g fragment.segments=accessKind g fragment.access.val := by
  have sameLast : fragment.access.val.getLast?=fragment.segments.getLast? := by
    rw [fragment.literal]
    cases actual : fragment.segments with
    | nil => have start := fragment.start;rw [actual] at start;cases start
    | cons e es => simp only [List.getLast?_append,List.getLast?_cons,Option.some_or]
  simp only [accessKind,sameLast]

theorem SourceEdgeFragment.fragment_typed
    (fragment : SourceEdgeFragment current g root edge position) :
    ∃ k,accessKind g fragment.segments=some k := by
  rw [fragment.fragment_kind]
  exact fragment.access.property.2.2

theorem SourceEdgeFragment.fragment_labels
    (fragment : SourceEdgeFragment current g root edge position) :
    ∃ a b,Labelling g fragment.segments a b := by
  obtain ⟨input,output,whole⟩ := fragment.access.property.1.1
  obtain ⟨middle,_beforeLabels,labels⟩ := fragment.assignments input output whole
  exact ⟨middle,output,labels⟩
end
end Lamping.AG
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

private theorem cancellation_proper_kept (cancel : IsCancellation s)
    (node : K⊕(Unit⊕Unit))
    (proper : (site.net.label node).sort=.op .app ∨(site.net.label node).sort=.op .lam) :
    ∃ k,node=Sum.inl k := by
  cases node with
  | inl k => exact ⟨k,rfl⟩
  | inr pair =>
    cases pair <;> rename_i u <;> cases u <;> cases cancel <;>
      rcases proper with wrong|wrong <;> cases wrong

private theorem child_proper {kind : Kind} {ctx out : Port kind}
    (roles : SyntaxChildPorts kind ctx out step) : kind=.op .app ∨kind=.op .lam := by
  cases roles
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem PathSite.cancellation_realized_outside (cancel : IsCancellation s)
    {current : LTerm} {root : B} {sourcePort : SourcePort} {endpoint : Endpoint site.net}
    (realizes : SourcePortRealizes current site.net root sourcePort endpoint) :
    ∃ cut : Endpoint (cutFragment site.net (pathPartition s V) site.closed),endpoint=site.outsideEnd cut := by
  cases realizes with
  | external => exact ⟨.inr (.inl (.inl root)),rfl⟩
  | @departure p term step port node ctx out lookup role parent word roles finish =>
    obtain ⟨k,same⟩ := cancellation_proper_kept site cancel node (child_proper roles)
    subst node
    exact ⟨.inl ⟨k,out⟩,rfl⟩
  | @appContext p origin fn arg node port lookup access word shape role finish =>
    obtain ⟨k,same⟩ := cancellation_proper_kept site cancel node (Or.inl shape)
    subst node
    exact ⟨.inl ⟨k,port⟩,rfl⟩
  | @lamContext p origin body node port lookup access word shape role finish =>
    obtain ⟨k,same⟩ := cancellation_proper_kept site cancel node (Or.inr shape)
    subst node
    exact ⟨.inl ⟨k,port⟩,rfl⟩
  | @binding p origin body node ctx port lookup parent word shape ctxRole bindRole finish =>
    obtain ⟨k,same⟩ := cancellation_proper_kept site cancel node (Or.inr shape)
    subst node
    exact ⟨.inl ⟨k,port⟩,rfl⟩
end
end Lamping.AG
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

theorem PathSite.cancellation_fragment_contract_actual (cancel : IsCancellation s) :
    ∃ principal : SiteActionPrincipal site,
    ∀ {current : LTerm} {root : B} {edge : SourceEdge} {position : Path}
      (fragment : SourceEdgeFragment current site.net root edge position) {a b : Context},
      Labelling site.net fragment.access.val a b →
      ∃ (middle : Context) (first terminal : Endpoint (cutFragment site.net (pathPartition s V) site.closed)) (es : List (Endpoint site.reduce)),
        fragment.fromEndpoint=site.outsideEnd first ∧fragment.toEndpoint=site.outsideEnd terminal ∧
        (fragment.before=[] ∧middle=a ∨Labelling site.net fragment.before a middle) ∧
        Labelling site.reduce es middle b ∧CanonicalCancellationResidual site
          (site.cancellation_canonical_fronts principal.edges) es fragment.segments ∧
        es.head?=some (plugLeft _ s.right.net first) ∧
        es.getLast?=some (site.reduce.wire (plugLeft _ s.right.net terminal)) := by
  obtain ⟨principal,contract⟩ := site.cancellation_canonical_source_contraction_with_routes cancel
  refine ⟨principal,?_⟩
  intro current root edge position fragment a b whole
  obtain ⟨first,sourceFrom⟩ := site.cancellation_realized_outside cancel fragment.fromRealizes
  obtain ⟨terminal,sourceTo⟩ := site.cancellation_realized_outside cancel fragment.toRealizes
  obtain ⟨middle,beforeLabels,labels⟩ := fragment.assignments a b whole
  let c := cutFragment site.net (pathPartition s V) site.closed
  have firstEq : fragment.segments.head?=some (site.outsideEnd first) := fragment.start.trans (congrArg some sourceFrom)
  have lastEq : fragment.segments.getLast?=some (site.outsideEnd (c.wire terminal)) := by
    rw [fragment.finish,sourceTo,site.outsideEnd_wire]
  obtain ⟨es,newLabels,residual,head,last⟩ := contract labels fragment.fragment_typed first (c.wire terminal) firstEq lastEq
  refine ⟨middle,first,terminal,es,sourceFrom,sourceTo,beforeLabels,newLabels,residual,head,?_⟩
  exact last.trans (congrArg some (plugLeft_wire c s.right.net terminal).symm)
end
end Lamping.AG
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

theorem PathSite.cancellation_canonical_root_accesses (cancel : IsCancellation s)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (root : B)
    (positive : boundary root=true) :
    ∃ principal : SiteActionPrincipal site,∀ old : RootAccess site.net root,
      ∃ reduced : RootAccess site.reduce root,
        accessWord site.reduce reduced.val=accessWord site.net old.val ∧
        accessKind site.reduce reduced.val=accessKind site.net old.val ∧
        CanonicalCancellationResidual site (site.cancellation_canonical_fronts principal.edges)
          reduced.val old.val := by
  obtain ⟨principal,contract⟩ := site.cancellation_canonical_source_contraction_with_routes cancel
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  refine ⟨principal,?_⟩
  intro old
  obtain ⟨terminal,role,level,finish,atPort,incoming⟩ := old.incoming_endpoint
  obtain ⟨node,p,nodeEq⟩ := site.cancellation_source_incoming_kept cancel atPort incoming
  rw [nodeEq] at finish
  let c := cutFragment site.net (pathPartition s V) site.closed
  let first : Endpoint c := .inr (.inl (.inl root))
  let last : Endpoint c := c.wire (.inl ⟨node,p⟩)
  have oldLast : old.val.getLast?=some (site.outsideEnd last) := by
    rw [←site.outsideEnd_wire]
    exact finish
  obtain ⟨a,b,oldLabels⟩ := old.property.1.1
  obtain ⟨es,newLabels,residual,newRoot,newLast⟩ :=
    contract oldLabels old.property.2.2 first last old.property.2.1 oldLast
  change es.head?=some (.inr (.inl root)) at newRoot
  have newEnd : es.getLast?=some (site.reduce.wire (.inl ⟨.inl node,p⟩)) := by
    simpa only [←plugLeft_wire c s.right.net (.inl ⟨node,p⟩)] using newLast
  have kind : accessKind site.reduce es=accessKind site.net old.val := by
    simp only [accessKind,finish,newEnd,Option.bind_some,Pairing.involutive]
    rfl
  have newForward := newLabels.root_forward_of_flow newFlow root newRoot positive
  obtain ⟨again,againLabels,_againResidual,againRoot,againLast,word⟩ :=
    site.cancellation_source_word_contraction cancel oldLabels old.property.1.2 old.property.2.2
      first last old.property.2.1 oldLast
  change again.head?=some (.inr (.inl root)) at againRoot
  have againForward := againLabels.root_forward_of_flow newFlow root againRoot positive
  obtain ⟨same,_input⟩ := Labelling.rooted_terminal_unique site.reduce newLabels newForward newRoot
    againLabels againForward againRoot (newLast.trans againLast.symm)
  let reduced : RootAccess site.reduce root := ⟨es,⟨⟨⟨a,b,newLabels⟩,newForward⟩,newRoot,by
    rw [kind]
    exact old.property.2.2⟩⟩
  refine ⟨reduced,?_,kind,residual⟩
  change accessWord site.reduce es=accessWord site.net old.val
  rw [same]
  exact word
end
end Lamping.AG

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

theorem PathSite.cancellation_occurrence_fragments (cancel : IsCancellation s)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (root : B)
    (positive : boundary root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase) :
    ∃ principal : SiteActionPrincipal site,∀ {position : Path}
      (source : OccurrenceFragment current site.net root position)
      (target : OccurrenceFragment current site.reduce root position),
      CanonicalCancellationResidual site (site.cancellation_canonical_fronts principal.edges)
        target.fragment.segments source.fragment.segments := by
  obtain ⟨principal,rootMap⟩ := site.cancellation_canonical_root_accesses cancel flow root positive
  refine ⟨principal,?_⟩
  intro position source target
  rcases source with ⟨sub,env,ctx,occurrence,source⟩
  rcases target with ⟨otherSub,otherEnv,otherCtx,otherOccurrence,target⟩
  obtain ⟨rfl,rfl,rfl⟩ := occurrence.same_occurrence otherOccurrence
  obtain ⟨newWhole,wholeWord,_kind,wholeResidual⟩ := rootMap source.access
  have fullEq : newWhole=target.access := targetMatches.accessWord_injective
    (wholeWord.trans (source.word.trans target.word.symm))
  rw [fullEq] at wholeResidual
  rcases occurrence.last_departure with ⟨empty,external⟩ |
    ⟨parentPath,step,parentTerm,split,lookup,role⟩
  · have externalEdge : (sourceEdge env ctx sub).fromPort=.external := by
      cases sub <;> exact external
    rw [source.external_segments externalEdge,target.external_segments externalEdge]
    exact wholeResidual
  · let parentPosition : Position current.erase := ⟨parentPath,by
      rw [←LTerm.erase_subterm,lookup];rfl⟩
    obtain ⟨parent,parentWord,_⟩ := Matches.observation site.net sourceMatches parentPosition
    obtain ⟨newParent,newParentWord,_kind,parentResidual⟩ := rootMap parent
    have sourceFrom : (sourceEdge env ctx sub).fromPort=ctx := by cases sub <;> rfl
    have actualRole : SourceDeparture parentTerm step (sourceEdge env ctx sub).fromPort := by
      rw [sourceFrom];exact role
    have oldWord : position=accessWord site.net parent.val++[step] := by rw [parentWord];exact split
    have newWord : position=accessWord site.reduce newParent.val++[step] := by rw [newParentWord];exact oldWord
    have oldCut := source.child_prefix sourceMatches actualRole parent oldWord
    have newCut := target.child_prefix targetMatches actualRole newParent newWord
    have nonempty : source.segments≠[] := by intro empty;have start:=source.start;rw [empty] at start;cases start
    obtain ⟨pre,post,newSplit,preResidual,postResidual⟩ :=
      CanonicalCancellationResidual.split_at_typed_prefix site cancel principal wholeResidual
        oldCut.2 parent.property.2.2 nonempty
    have prefixEq : pre=newParent.val :=
      CanonicalCancellationResidual.target_unique site cancel principal preResidual parentResidual
    rw [prefixEq] at newSplit
    have pieces : target.segments=post := List.append_cancel_left (newCut.2.symm.trans newSplit)
    rw [pieces]
    exact postResidual
end
end Lamping.AG
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- Comparison of actual occurrence fragments, not just independently
chosen contracted paths. Both Matches hypotheses are explicit semantics. -/
theorem PathSite.cancellation_occurrence_equality (cancel : IsCancellation s)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (root : B)
    (positive : boundary root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (sourceFirst : OccurrenceFragment current site.net root p)
    (targetFirst : OccurrenceFragment current site.reduce root p)
    (sourceSecond : OccurrenceFragment current site.net root q)
    (targetSecond : OccurrenceFragment current site.reduce root q) :
    targetFirst.fragment.segments=targetSecond.fragment.segments ↔
      sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  obtain ⟨principal,relations⟩ := site.cancellation_occurrence_fragments cancel flow root positive
    sourceMatches targetMatches
  exact CanonicalCancellationResidual.equality_iff site cancel principal
    (relations sourceFirst targetFirst) (relations sourceSecond targetSecond)
end
end Lamping.AG