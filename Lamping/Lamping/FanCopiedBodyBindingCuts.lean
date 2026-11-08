import Lamping.Lamping.FanCopiedBindingCuts
import Lamping.Lamping.FanCopiedLambdaBodyPrefixes
import Lamping.Lamping.ActionRawOutsideCut
import Lamping.Lamping.ActualFragmentFanUniqueness
set_option maxHeartbeats 4000000
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.lam i j lt) V) site.closed
private abbrev bodyBindingRight (i j : Nat) (lt : i<j) := (Schema.fanAction Op.lam i j lt).right.net
local notation "rhs" => bodyBindingRight i j lt
local notation "writer2" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "pivot" => (Sum.inr (Sum.inl (Sum.inr (Sum.inr true))) : Endpoint cut)
local notation "oldBody" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) (Sum.inr true)) : Endpoint site.net)
/-- The actual binding trim and copied BODY prefix determine one literal
ordinal cut. Its OLD suffix is THIS entire source fragment. -/
theorem SourceEdgeFragment.fan_copied_body_binding_cut
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
    (childFinish : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),lamBind⟩)))
    {a b : Context} (labels : Labelling site.reduce target.access.val a b) :
    ∃ pending : PendingRhsBlock cut rhs (target.access.val.map (plugEnd (cut).label (rhs).label).invFun) a b,
      ∃ (rawTail : List (PlugSegment cut rhs)) (oldTail : List (Endpoint site.net)) (seam : Context),
      source.segments=oldBody::oldTail ∧
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=
        Sum.inr (Sum.inl ⟨Sum.inl parentBranch,Sum.inr true⟩)::writer2::Sum.inl pivot::
          (rawTail++[.inr (.inr (.inl (.inr false))),.inr (.inl ⟨.inr false,.inr childBranch⟩)]) ∧
      ActionCanonicalBlocks site principal (Sum.inl pivot::rawTail) (oldBody::oldTail) ∧
      PlugLabelling cut rhs (Sum.inl pivot::rawTail) seam pending.middle ∧
      ActionCanonicalBlocks site principal pending.pre source.access.val ∧
      target.access.val.map (plugEnd (cut).label (rhs).label).invFun=pending.pre++
        [.inr (.inr (.inl (.inr false))),.inr (.inl ⟨.inr false,.inr childBranch⟩)] := by
  obtain ⟨pending,whole,_sourceLabels,_sourceEnd,trimmed⟩ :=
    site.fan_aux_canonical_access flow root positive sourceMatches principal source.access target.access
      (source.word.trans target.word.symm) childBranch false childFinish labels
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨middle,assignment,pieceLabels⟩ := target.assignments a b labels
  rw [targetCut.1] at assignment
  have parentLabels : Labelling site.reduce targetParent.val a middle := by
    rcases assignment with ⟨empty,_⟩|actual
    · have head:=targetParent.property.2.1;rw [empty] at head;cases head
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
  have literal : (initial++[Sum.inl pivot])++tail=pending.pre++
      [.inr (.inr (.inl (.inr false))),.inr (.inl ⟨.inr false,.inr childBranch⟩)] := by
    dsimp only [initial]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
    rw [←targetShape,←List.map_append,←targetCut.2]
    exact trimmed
  obtain ⟨rawTail,prefixSplit,tailSplit⟩ := trim_after_literal_pivot initial tail pending.pre (Sum.inl pivot)
    (.inr (.inr (.inl (.inr false)))) (.inr (.inl ⟨.inr false,.inr childBranch⟩))
    literal (by intro h;cases h) (by intro h;cases h)
  have rawSplit : pending.pre=(initial++[Sum.inl pivot])++rawTail := prefixSplit
  have parentLast : (initial++[Sum.inl pivot]).getLast?=some (Sum.inl pivot) := by
    simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
  have parentRelation : ActionCanonicalBlocks site principal (initial++[Sum.inl pivot])
      (sourceParent.val++[oldBody]) := by
    simpa only [initial,List.append_assoc] using parent
  obtain ⟨oldTail,seam,oldSplit,relation,_sameParentLabels,newLabels⟩ :=
    whole.cut_at_raw_parent site parentRelation pending.prefixPath.labelling rawSplit pivot parentLast
  have sourceCut := (source.child_prefix sourceMatches role sourceParent sourceWord).2
  have sourcePiece : source.segments=oldBody::oldTail := by
    apply List.append_cancel_left (as:=sourceParent.val)
    rw [←sourceCut]
    simpa only [List.append_assoc,List.singleton_append] using oldSplit
  change ActionCanonicalBlocks site principal (Sum.inl pivot::rawTail) (oldBody::oldTail) at relation
  exact ⟨pending,rawTail,oldTail,seam,sourcePiece,by rw [targetShape,tailSplit],relation,newLabels,whole,trimmed⟩

/-- Independent parent/child Bool synchronization is supplied only at this
LOW boundary. Canonical uniqueness uses the real source fragment's NoPassive. -/
theorem SourceEdgeFragment.fan_copied_body_binding_forward
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceFirst : SourceEdgeFragment current site.net root leftEdge p)
    (targetFirst : SourceEdgeFragment current site.reduce root leftEdge p)
    (sourceSecond : SourceEdgeFragment current site.net root rightEdge q)
    (targetSecond : SourceEdgeFragment current site.reduce root rightEdge q)
    (leftRole : SourceDeparture leftTerm .body leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm .body rightEdge.fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[.body])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[.body])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[.body])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[.body])
    (parentBranch childBranch : Bool)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl parentBranch),.inl ()⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl parentBranch),.inl ()⟩)))
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),lamBind⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),lamBind⟩)))
    (pieces : sourceFirst.segments=sourceSecond.segments) : targetFirst.segments=targetSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨_lp,leftRaw,_leftOld,ls,leftSource,leftShape,leftRelation,leftPieceLabels,_leftWhole,_leftTrim⟩ :=
    sourceFirst.fan_copied_body_binding_cut site flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord parentBranch childBranch leftParentAt leftEndAt leftLabels
  obtain ⟨_rp,rightRaw,_rightOld,rs,rightSource,rightShape,rightRelation,rightPieceLabels,_rightWhole,_rightTrim⟩ :=
    sourceSecond.fan_copied_body_binding_cut site flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord parentBranch childBranch rightParentAt rightEndAt rightLabels
  have rawSame := sourceFirst.fan_target_unique_of_contiguous_source site leftRelation rightRelation
    leftPieceLabels rightPieceLabels (leftSource.symm.trans (pieces.trans rightSource))
    (pre:=[]) (post:=[]) (by simpa only [List.nil_append,List.append_nil] using leftSource)
  have tails := (List.cons.inj rawSame).2
  have maps : targetFirst.segments.map (plugEnd (cut).label (rhs).label).invFun=
      targetSecond.segments.map (plugEnd (cut).label (rhs).label).invFun := by
    rw [leftShape,rightShape,tails]
  have physical := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label)) maps
  simpa only [plug_decomposition_flatten] using physical
end
end Lamping.AG
#print axioms Lamping.AG.SourceEdgeFragment.fan_copied_body_binding_cut
#print axioms Lamping.AG.SourceEdgeFragment.fan_copied_body_binding_forward