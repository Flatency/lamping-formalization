import Lamping.Lamping.FanAppCopiedArgumentCuts
import Lamping.Lamping.FanAppCopiedContextCuts
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.fanAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.app i j lt) V) site.closed
private abbrev argumentContextRight (i j : Nat) (lt : i<j) := (Schema.fanAction Op.app i j lt).right.net
local notation "rhs" => argumentContextRight i j lt
variable (parentBranch childBranch : Bool)
local notation "argumentSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl parentBranch) appArg)) : PlugSegment cut rhs)
local notation "writerSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "exitPivot" => (Sum.inr (Sum.inl (Sum.inr (Sum.inr true))) : Endpoint cut)
local notation "oldArgument" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) appArg) : Endpoint site.net)
local notation "readerTail" => ([Sum.inr (Sum.inr (Sum.inl (Sum.inr false))),Sum.inr (Sum.inl (Sigma.mk (Sum.inr false) (Sum.inr childBranch)))] : List (PlugSegment cut rhs))

/-- Two-ended finite normalization of an actual copied-APP ARG edge
ending at copied APP context. Both seams and the OLD split come from the
same whole assignment; the outside writer pivot excludes reader overlap. -/
theorem SourceEdgeFragment.fan_copied_argument_copied_app_context_cut
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm .arg edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[.arg])
    (targetWord : position=accessWord site.reduce targetParent.val++[.arg])
    (parentFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl parentBranch),appCtx⟩)))
    (endFinish : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),appCtx⟩)))
    {a b : Context} (wholeLabels : Labelling site.reduce target.access.val a b) :
    ∃ pending : PendingRhsBlock cut rhs (target.access.val.map (plugEnd (cut).label (rhs).label).invFun) a b,
      ∃ rawTail oldTail seam,
      pending.pre=(targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[argumentSegment,writerSegment,Sum.inl exitPivot])++rawTail ∧
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=[argumentSegment,writerSegment,Sum.inl exitPivot]++rawTail++readerTail ∧
      source.segments=oldArgument::oldTail ∧
      ActionCanonicalBlocks site principal (Sum.inl exitPivot::rawTail) (site.outsideEnd exitPivot::oldTail) ∧
      PlugLabelling cut rhs (Sum.inl exitPivot::rawTail) seam pending.middle := by
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨pieceInput,prefixLabels,pieceLabels⟩ := target.assignments a b wholeLabels
  rw [targetCut.1] at prefixLabels
  have parentLabels : Labelling site.reduce targetParent.val a pieceInput := by
    rcases prefixLabels with ⟨empty,_⟩|actual
    · have head := targetParent.property.2.1;rw [empty] at head;cases head
    · exact actual
  obtain ⟨rawFullTail,_writerOutput,targetShape,_writerRule,_targetTailLabels⟩ := fan_app_copied_argument_fragment cut i j parentBranch targetMatches target role targetParent targetWord parentFinish pieceLabels
  change List (PlugSegment cut rhs) at rawFullTail
  change target.segments.map (plugEnd (cut).label (rhs).label).invFun=[argumentSegment,writerSegment,Sum.inl exitPivot]++rawFullTail at targetShape
  obtain ⟨pending,whole,_sourceLabels,_sourceFinish,trimmed⟩ := site.fan_aux_canonical_access
    flow root positive sourceMatches principal source.access target.access
    (source.word.trans target.word.symm) childBranch false endFinish wholeLabels
  change PendingRhsBlock cut rhs (target.access.val.map (plugEnd (cut).label (rhs).label).invFun) a b at pending
  have untrimmed : ((targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[argumentSegment,writerSegment])++
      [Sum.inl exitPivot])++rawFullTail=pending.pre++readerTail := by
    rw [←trimmed,targetCut.2,List.map_append,targetShape]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  obtain ⟨rawTail,trimmedSplit,tailSplit⟩ := trim_after_literal_pivot
    (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[argumentSegment,writerSegment])
    rawFullTail pending.pre (Sum.inl exitPivot)
    (.inr (.inr (.inl (.inr false)))) (.inr (.inl ⟨.inr false,.inr childBranch⟩))
    untrimmed (by intro wrong;cases wrong) (by intro wrong;cases wrong)
  have rawSplit : pending.pre=(targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[argumentSegment,writerSegment,Sum.inl exitPivot])++rawTail := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using trimmedSplit
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  have parent := site.fan_app_argument_padding_access flow root positive sourceMatches principal
    sourceParent targetParent parentWord parentBranch parentFinish parentLabels
  have parentLast : (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[argumentSegment,writerSegment,Sum.inl exitPivot]).getLast?=
      some (Sum.inl exitPivot) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨oldTail,seam,oldSplit,relation,_actualParentLabels,actualPieceLabels⟩ :=
    whole.cut_at_raw_parent site parent pending.prefixPath.labelling rawSplit exitPivot parentLast
  have sourceCut := source.child_prefix sourceMatches role sourceParent sourceWord
  have sourceShape : source.segments=oldArgument::oldTail := by
    apply List.append_cancel_left (as:=sourceParent.val)
    rw [←sourceCut.2,oldSplit]
    simp only [List.append_assoc,List.singleton_append]
  refine ⟨pending,rawTail,oldTail,seam,rawSplit,?_,sourceShape,relation,actualPieceLabels⟩
  rw [targetShape,tailSplit]
  simp only [List.append_assoc]
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.app i j lt) V) site.closed
local notation "rhs" => fanRight Op.app i j
theorem SourceEdgeFragment.fan_copied_argument_copied_app_context_forward
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceFirst : SourceEdgeFragment current site.net root leftEdge p)
    (targetFirst : SourceEdgeFragment current site.reduce root leftEdge p)
    (sourceSecond : SourceEdgeFragment current site.net root rightEdge q)
    (targetSecond : SourceEdgeFragment current site.reduce root rightEdge q)
    (leftRole : SourceDeparture leftTerm .arg leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm .arg rightEdge.fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[.arg])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[.arg])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[.arg])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[.arg])
    (parentBranch childBranch : Bool)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl parentBranch),appCtx⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl parentBranch),appCtx⟩)))
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),appCtx⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),appCtx⟩)))
    (pieces : sourceFirst.segments=sourceSecond.segments) : targetFirst.segments=targetSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨lp,lr,lo,ls,_leftSplit,leftShape,leftSource,leftRelation,leftPieceLabels⟩ :=
    sourceFirst.fan_copied_argument_copied_app_context_cut site parentBranch childBranch flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord leftParentAt leftEndAt leftLabels
  obtain ⟨rp,rr,ro,rs,_rightSplit,rightShape,rightSource,rightRelation,rightPieceLabels⟩ :=
    sourceSecond.fan_copied_argument_copied_app_context_cut site parentBranch childBranch flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord rightParentAt rightEndAt rightLabels
  have oldTails := (List.cons.inj (leftSource.symm.trans (pieces.trans rightSource))).2
  have sameOld : site.outsideEnd (.inr (.inl (.inr (.inr true))))::lo=
      site.outsideEnd (.inr (.inl (.inr (.inr true))))::ro := congrArg (_::·) oldTails
  have contiguous : sourceFirst.segments=[]++
      (site.outsideEnd (.inr (.inl (.inr (.inr true))))::lo)++[] := by
    simpa only [List.append_nil] using leftSource
  have rawSame := sourceFirst.fan_target_unique_of_contiguous_source site leftRelation rightRelation
    leftPieceLabels rightPieceLabels sameOld contiguous
  have tails := (List.cons.inj rawSame).2
  have maps : targetFirst.segments.map (plugEnd (cut).label (rhs).label).invFun=
      targetSecond.segments.map (plugEnd (cut).label (rhs).label).invFun := by
    change targetFirst.segments.map (plugEnd (cut).label (rhs).label).invFun=_ at leftShape
    change targetSecond.segments.map (plugEnd (cut).label (rhs).label).invFun=_ at rightShape
    rw [leftShape,rightShape,tails]
  have physical := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label)) maps
  simpa only [plug_decomposition_flatten] using physical
end
end Lamping.AG
#print axioms Lamping.AG.SourceEdgeFragment.fan_copied_argument_copied_app_context_cut
#print axioms Lamping.AG.SourceEdgeFragment.fan_copied_argument_copied_app_context_forward
