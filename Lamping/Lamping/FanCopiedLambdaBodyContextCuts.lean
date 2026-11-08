import Lamping.Lamping.FanCopiedLambdaBodyPrefixes
import Lamping.Lamping.ActionRawOutsideCut
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.lam i j lt) V) site.closed
private abbrev bodyContextRight (i j : Nat) (lt : i<j) := (Schema.fanAction Op.lam i j lt).right.net
local notation "rhs" => bodyContextRight i j lt
local notation "writer2" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "pivot" => (Sum.inr (Sum.inl (Sum.inr (Sum.inr true))) : Endpoint cut)
local notation "oldBody" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) (Sum.inr true)) : Endpoint site.net)
/-- The normalized OLD path is a contiguous part of THIS source fragment.
The parent padding is only a real whole-prefix used to select its ordinal. -/
theorem SourceEdgeFragment.fan_copied_body_context_cut
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm .body edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[.body])
    (targetWord : position=accessWord site.reduce targetParent.val++[.body])
    (parentBranch childBranch : Bool)
    (parentFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl parentBranch),.inl ()⟩)))
    (childFinish : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),.inl ()⟩)))
    {a b : Context} (labels : Labelling site.reduce target.access.val a b) :
    ∃ (rawTail : List (PlugSegment cut rhs)) (oldTail : List (Endpoint site.net)) (seam : Context),
      source.segments=(oldBody::oldTail)++principal.edges ∧
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=
        Sum.inr (Sum.inl ⟨Sum.inl parentBranch,Sum.inr true⟩)::writer2::Sum.inl pivot::
          (rawTail++[Sum.inr (Sum.inr (Sum.inl (Sum.inl childBranch)))]) ∧
      ActionCanonicalBlocks site principal (Sum.inl pivot::rawTail) (oldBody::oldTail) ∧
      PlugLabelling cut rhs (Sum.inl pivot::rawTail) seam b := by
  obtain ⟨pending,oldPre,contexts,whole,_oldLabels,wholeSplit,_oldLast,trimmed⟩ :=
    site.fan_lambda_context_canonical_trim flow root positive sourceMatches principal source.access target.access
      (source.word.trans target.word.symm) childBranch childFinish labels
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨middle,assignment,pieceLabels⟩ := target.assignments a b labels
  rw [targetCut.1] at assignment
  have parentLabels : Labelling site.reduce targetParent.val a middle := by
    rcases assignment with ⟨empty,_⟩|actual
    · have head := targetParent.property.2.1;rw [empty] at head;cases head
    · exact actual
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  obtain ⟨parent,_parentPaddedLabels⟩ := site.fan_lambda_body_parent_canonical flow root positive
    sourceMatches principal sourceParent targetParent parentWord parentBranch parentFinish parentLabels
  obtain ⟨tail,_writerMiddle,targetShape,_writerRule,_tailLabels⟩ :=
    fan_copied_lambda_body_fragment cut i j parentBranch targetMatches target role targetParent targetWord parentFinish pieceLabels
  change List (PlugSegment cut rhs) at tail
  change target.segments.map (plugEnd (cut).label (rhs).label).invFun=
    Sum.inr (Sum.inl ⟨Sum.inl parentBranch,Sum.inr true⟩)::writer2::Sum.inl pivot::tail at targetShape
  let initial := targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
    [Sum.inr (Sum.inl ⟨Sum.inl parentBranch,Sum.inr true⟩),writer2]
  have literal : (initial++[Sum.inl pivot])++tail=
      pending.pre++[Sum.inr (Sum.inr (Sum.inl (Sum.inl childBranch)))] := by
    dsimp only [initial]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
    rw [←targetShape,←List.map_append,←targetCut.2]
    exact trimmed
  have extended := congrArg (fun xs=>xs++[Sum.inr (Sum.inr (Sum.inl (Sum.inl childBranch)))]) literal
  simp only [List.append_assoc,List.singleton_append] at extended
  obtain ⟨rawTail,prefixSplit,tailExtra⟩ := trim_after_literal_pivot initial
    (tail++[Sum.inr (Sum.inr (Sum.inl (Sum.inl childBranch)))]) pending.pre (Sum.inl pivot)
    (Sum.inr (Sum.inr (Sum.inl (Sum.inl childBranch)))) (Sum.inr (Sum.inr (Sum.inl (Sum.inl childBranch))))
    (by simpa only [List.append_assoc] using extended) (by intro h;cases h) (by intro h;cases h)
  have tailSplit : tail=rawTail++[Sum.inr (Sum.inr (Sum.inl (Sum.inl childBranch)))] :=
    List.append_cancel_right (by simpa only [List.append_assoc] using tailExtra)
  have rawSplit : pending.pre=(initial++[Sum.inl pivot])++rawTail := prefixSplit
  have parentLast : (initial++[Sum.inl pivot]).getLast?=some (Sum.inl pivot) := by
    simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
  have parentRelation : ActionCanonicalBlocks site principal (initial++[Sum.inl pivot])
      (sourceParent.val++[oldBody]) := by
    simpa only [initial,List.append_assoc] using parent
  obtain ⟨oldTail,seam,oldSplit,relation,_sameParentLabels,newLabels⟩ :=
    whole.cut_at_raw_parent site parentRelation pending.prefixPath.labelling rawSplit pivot parentLast
  have sourceCut := (source.child_prefix sourceMatches role sourceParent sourceWord).2
  rw [oldSplit,List.append_assoc] at wholeSplit
  have sourcePiece : source.segments=(oldBody::oldTail)++principal.edges := by
    apply List.append_cancel_left (as:=sourceParent.val)
    rw [←sourceCut]
    simpa only [List.append_assoc,List.singleton_append] using wholeSplit
  change ActionCanonicalBlocks site principal (Sum.inl pivot::rawTail) (oldBody::oldTail) at relation
  rw [contexts] at newLabels
  exact ⟨rawTail,oldTail,seam,sourcePiece,by rw [targetShape,tailSplit],relation,newLabels⟩
end
end Lamping.AG
#print axioms Lamping.AG.SourceEdgeFragment.fan_copied_body_context_cut
