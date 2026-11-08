import Lamping.Lamping.FanAppCopiedFunctionCuts
import Lamping.Lamping.ActualFragmentFanUniqueness
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "s" => Schema.fanAction Op.app i j lt
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed
private abbrev contextFanRight (i j : Nat) (lt : i<j) := (Schema.fanAction Op.app i j lt).right.net
local notation "rhs" => contextFanRight i j lt

theorem SourceEdgeFragment.fan_kept_parent_copied_app_context_cut
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {edge : SourceEdge} {position : Path}
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm step edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[step])
    (targetWord : position=accessWord site.reduce targetParent.val++[step])
    (parentNode : K) (parentPort : Port (kept parentNode).sort)
    (parentEnd : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inl parentNode,parentPort⟩)))
    (branch : Bool)
    (endAt : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inr false⟩)))
    {a b : Context} (labels : Labelling site.reduce target.access.val a b) :
    ∃ pivot : Endpoint cut,∃ rawPiece : List (PlugSegment cut rhs),∃ seam output : Context,
      sourceParent.val.getLast?=some (site.outsideEnd pivot) ∧
      targetParent.val.getLast?=some (AG.plugLeft cut rhs pivot) ∧
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=rawPiece++
        [.inr (.inr (.inl (.inr false))),.inr (.inl ⟨.inr false,.inr branch⟩)] ∧
      ActionCanonicalBlocks site principal (Sum.inl pivot::rawPiece)
        (site.outsideEnd pivot::source.segments) ∧
      PlugLabelling cut rhs (Sum.inl pivot::rawPiece) seam output := by
  obtain ⟨pending,whole,_sourceLabels,_sourceEnd,trimmed⟩ :=
    site.fan_aux_canonical_access flow root positive sourceMatches principal source.access target.access
      (source.word.trans target.word.symm) branch false endAt labels
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨middle,assignment,_pieceLabels⟩ := target.assignments a b labels
  rw [targetCut.1] at assignment
  have parentLabels : Labelling site.reduce targetParent.val a middle := by
    rcases assignment with ⟨empty,_⟩ | actual
    · have head := targetParent.property.2.1;rw [empty] at head;cases head
    · exact actual
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  obtain ⟨parent,_parentLabels,parentFinish⟩ :=
    site.action_kept_canonical_access (.fan .app i j lt) flow root positive sourceMatches principal
      sourceParent targetParent parentWord parentNode parentPort parentEnd parentLabels
  let pivot : Endpoint cut := (cut).wire (.inl ⟨parentNode,parentPort⟩)
  have oldLast : sourceParent.val.getLast?=some (site.outsideEnd pivot) := by
    change sourceParent.val.getLast?=some (site.outsideEnd ((cut).wire (.inl ⟨parentNode,parentPort⟩)))
    rw [←site.outsideEnd_wire];exact parentFinish
  have newLast : targetParent.val.getLast?=some (AG.plugLeft cut rhs pivot) :=
    parentEnd.trans (congrArg some (plugLeft_wire cut rhs (.inl ⟨parentNode,parentPort⟩)))
  have rawLast : (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun).getLast?=
      some (Sum.inl pivot) := by
    rw [List.getLast?_map,newLast]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl pivot))
  obtain ⟨initial,parentShape⟩ := List.getLast?_eq_some_iff.mp rawLast
  have untrimmed : (initial++[Sum.inl pivot])++
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=pending.pre++
        [.inr (.inr (.inl (.inr false))),.inr (.inl ⟨.inr false,.inr branch⟩)] := by
    rw [←parentShape,←List.map_append,←targetCut.2]
    exact trimmed
  obtain ⟨rawPiece,prefixSplit,pieceSplit⟩ := trim_after_literal_pivot initial
    (target.segments.map (plugEnd (cut).label (rhs).label).invFun) pending.pre (Sum.inl pivot)
    (.inr (.inr (.inl (.inr false)))) (.inr (.inl ⟨.inr false,.inr branch⟩))
    untrimmed (by intro wrong;cases wrong) (by intro wrong;cases wrong)
  have rawSplit : pending.pre=
      targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++rawPiece := by
    rw [parentShape];exact prefixSplit
  obtain ⟨oldPiece,seam,oldSplit,relation,_sameParentLabels,pieceLabels⟩ :=
    whole.cut_at_raw_parent site parent pending.prefixPath.labelling rawSplit pivot rawLast
  have sourceCut := (source.child_prefix sourceMatches role sourceParent sourceWord).2
  have samePiece : oldPiece=source.segments := List.append_cancel_left (oldSplit.symm.trans sourceCut)
  rw [samePiece] at relation
  exact ⟨pivot,rawPiece,seam,pending.middle,oldLast,newLast,pieceSplit,relation,pieceLabels⟩
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.fanAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.app i j lt) V) site.closed
private abbrev doubleFanFunctionRight (i j : Nat) (lt : i<j) := (Schema.fanAction Op.app i j lt).right.net
local notation "rhs" => doubleFanFunctionRight i j lt
variable (parentBranch childBranch : Bool)
local notation "functionSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl parentBranch) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "exitPivot" => (Sum.inr (Sum.inl (Sum.inr (Sum.inl parentBranch))) : Endpoint cut)
local notation "activeAux" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) (Sum.inr parentBranch)) : Endpoint site.net)
local notation "readerTail" => ([Sum.inr (Sum.inr (Sum.inl (Sum.inr false))),Sum.inr (Sum.inl (Sigma.mk (Sum.inr false) (Sum.inr childBranch)))] : List (PlugSegment cut rhs))

/-- Two-ended finite normalization of an actual copied-APP function edge
ending at copied APP context. Both seams and the OLD split come from the
same whole assignment; the outside writer pivot excludes reader overlap. -/
theorem SourceEdgeFragment.fan_copied_function_copied_app_context_cut
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm .fn edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[.fn])
    (targetWord : position=accessWord site.reduce targetParent.val++[.fn])
    (parentFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl parentBranch),appCtx⟩)))
    (endFinish : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),appCtx⟩)))
    {a b : Context} (wholeLabels : Labelling site.reduce target.access.val a b) :
    ∃ pending : PendingRhsBlock cut rhs (target.access.val.map (plugEnd (cut).label (rhs).label).invFun) a b,
      ∃ rawTail oldTail seam,
      pending.pre=(targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[functionSegment,Sum.inl exitPivot])++rawTail ∧
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=[functionSegment,Sum.inl exitPivot]++rawTail++readerTail ∧
      source.segments=reverseEdges principal.edges++activeAux::oldTail ∧
      ActionCanonicalBlocks site principal (Sum.inl exitPivot::rawTail) (site.outsideEnd exitPivot::oldTail) ∧
      PlugLabelling cut rhs (Sum.inl exitPivot::rawTail) seam pending.middle := by
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨pieceInput,prefixLabels,pieceLabels⟩ := target.assignments a b wholeLabels
  rw [targetCut.1] at prefixLabels
  have parentLabels : Labelling site.reduce targetParent.val a pieceInput := by
    rcases prefixLabels with ⟨empty,_⟩|actual
    · have head := targetParent.property.2.1;rw [empty] at head;cases head
    · exact actual
  obtain ⟨rawFullTail,targetShape,_targetTailLabels⟩ := fan_app_copied_function_fragment cut i j targetMatches target role targetParent targetWord parentBranch parentFinish pieceLabels
  change List (PlugSegment cut rhs) at rawFullTail
  change target.segments.map (plugEnd (cut).label (rhs).label).invFun=[functionSegment,Sum.inl exitPivot]++rawFullTail at targetShape
  obtain ⟨pending,whole,_sourceLabels,_sourceFinish,trimmed⟩ := site.fan_aux_canonical_access
    flow root positive sourceMatches principal source.access target.access
    (source.word.trans target.word.symm) childBranch false endFinish wholeLabels
  change PendingRhsBlock cut rhs (target.access.val.map (plugEnd (cut).label (rhs).label).invFun) a b at pending
  have untrimmed : ((targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[functionSegment])++
      [Sum.inl exitPivot])++rawFullTail=pending.pre++readerTail := by
    rw [←trimmed,targetCut.2,List.map_append,targetShape]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  obtain ⟨rawTail,trimmedSplit,tailSplit⟩ := trim_after_literal_pivot
    (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[functionSegment])
    rawFullTail pending.pre (Sum.inl exitPivot)
    (.inr (.inr (.inl (.inr false)))) (.inr (.inl ⟨.inr false,.inr childBranch⟩))
    untrimmed (by intro wrong;cases wrong) (by intro wrong;cases wrong)
  have rawSplit : pending.pre=(targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[functionSegment,Sum.inl exitPivot])++rawTail := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using trimmedSplit
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  have parent := site.fan_app_function_padding_access flow root positive sourceMatches principal
    sourceParent targetParent parentWord parentBranch parentFinish parentLabels
  have parentLast : (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[functionSegment,Sum.inl exitPivot]).getLast?=
      some (Sum.inl exitPivot) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨oldTail,seam,oldSplit,relation,_actualParentLabels,actualPieceLabels⟩ :=
    whole.cut_at_raw_parent site parent pending.prefixPath.labelling rawSplit exitPivot parentLast
  have sourceCut := source.child_prefix sourceMatches role sourceParent sourceWord
  have sourceShape : source.segments=reverseEdges principal.edges++activeAux::oldTail := by
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
private theorem context_outside_injective : Function.Injective site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition (.fanAction .app i j lt) V)
  have mapped := congrArg split same
  change split (split.invFun (.inl e))=split (split.invFun (.inl f)) at mapped
  simpa only [split.right_inv,Sum.inl.injEq] using mapped

theorem SourceEdgeFragment.fan_kept_parent_copied_app_context_forward
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceFirst : SourceEdgeFragment current site.net root leftEdge p)
    (targetFirst : SourceEdgeFragment current site.reduce root leftEdge p)
    (sourceSecond : SourceEdgeFragment current site.net root rightEdge q)
    (targetSecond : SourceEdgeFragment current site.reduce root rightEdge q)
    (leftRole : SourceDeparture leftTerm leftStep leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm rightStep rightEdge.fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[leftStep])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[rightStep])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[leftStep])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[rightStep])
    (leftParent rightParent : NodePort signature K kept)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftParent.1,leftParent.2⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightParent.1,rightParent.2⟩)))
    (childBranch : Bool)
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),appCtx⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),appCtx⟩)))
    (pieces : sourceFirst.segments=sourceSecond.segments) : targetFirst.segments=targetSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨lp,lr,ls,lo,leftOldLast,_leftNewLast,leftShape,leftRelation,leftPieceLabels⟩ :=
    sourceFirst.fan_kept_parent_copied_app_context_cut site flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord leftParent.1 leftParent.2 leftParentAt childBranch leftEndAt leftLabels
  obtain ⟨rp,rr,rs,ro,rightOldLast,_rightNewLast,rightShape,rightRelation,rightPieceLabels⟩ :=
    sourceSecond.fan_kept_parent_copied_app_context_cut site flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord rightParent.1 rightParent.2 rightParentAt childBranch rightEndAt rightLabels
  have parentSeams := SourceEdgeFragment.equal_piece_parent_seams sourceMatches sourceFirst sourceSecond
    leftRole rightRole sourceLeft sourceRight sourceLeftWord sourceRightWord pieces
  have pivotEq : lp=rp := context_outside_injective site
    (Option.some.inj (leftOldLast.symm.trans (parentSeams.trans rightOldLast)))
  subst rp
  rw [←pieces] at rightRelation
  obtain ⟨x,y,parentLabels⟩ := targetLeft.property.1.1
  have word : accessWord site.net sourceLeft.val=accessWord site.reduce targetLeft.val :=
    List.append_cancel_right (sourceLeftWord.symm.trans targetLeftWord)
  obtain ⟨_,_,sourceParentFinish⟩ := site.action_kept_canonical_access (.fan .app i j lt)
    flow root positive sourceMatches principal sourceLeft targetLeft word leftParent.1 leftParent.2 leftParentAt parentLabels
  have rawSame := (sourceFirst.fan_target_unique_of_kept_parent_fragment site sourceMatches leftRole sourceLeft
    sourceLeftWord leftParent.1 leftParent.2 sourceParentFinish lp leftOldLast
    leftRelation rightRelation leftPieceLabels rightPieceLabels).2
  have tails := (List.cons.inj rawSame).2
  have maps : targetFirst.segments.map (plugEnd (cut).label (rhs).label).invFun=
      targetSecond.segments.map (plugEnd (cut).label (rhs).label).invFun := by
    change targetFirst.segments.map (plugEnd (cut).label (rhs).label).invFun=_ at leftShape
    change targetSecond.segments.map (plugEnd (cut).label (rhs).label).invFun=_ at rightShape
    rw [leftShape,rightShape,tails]
  have physical := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label)) maps
  simpa only [plug_decomposition_flatten] using physical

theorem SourceEdgeFragment.fan_copied_function_copied_app_context_forward
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceFirst : SourceEdgeFragment current site.net root leftEdge p)
    (targetFirst : SourceEdgeFragment current site.reduce root leftEdge p)
    (sourceSecond : SourceEdgeFragment current site.net root rightEdge q)
    (targetSecond : SourceEdgeFragment current site.reduce root rightEdge q)
    (leftRole : SourceDeparture leftTerm .fn leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm .fn rightEdge.fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[.fn])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[.fn])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[.fn])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[.fn])
    (parentBranch childBranch : Bool)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl parentBranch),appCtx⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl parentBranch),appCtx⟩)))
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),appCtx⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),appCtx⟩)))
    (pieces : sourceFirst.segments=sourceSecond.segments) : targetFirst.segments=targetSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨lp,lr,lo,ls,_leftSplit,leftShape,leftSource,leftRelation,leftPieceLabels⟩ :=
    sourceFirst.fan_copied_function_copied_app_context_cut site parentBranch childBranch flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord leftParentAt leftEndAt leftLabels
  obtain ⟨rp,rr,ro,rs,_rightSplit,rightShape,rightSource,rightRelation,rightPieceLabels⟩ :=
    sourceSecond.fan_copied_function_copied_app_context_cut site parentBranch childBranch flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord rightParentAt rightEndAt rightLabels
  have oldTails := (List.cons.inj (List.append_cancel_left (leftSource.symm.trans (pieces.trans rightSource)))).2
  have sameOld : site.outsideEnd (.inr (.inl (.inr (.inl parentBranch))))::lo=
      site.outsideEnd (.inr (.inl (.inr (.inl parentBranch))))::ro := congrArg (_::·) oldTails
  have contiguous : sourceFirst.segments=reverseEdges principal.edges++
      (site.outsideEnd (.inr (.inl (.inr (.inl parentBranch))))::lo)++[] := by
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
#print axioms Lamping.AG.SourceEdgeFragment.fan_kept_parent_copied_app_context_cut
#print axioms Lamping.AG.SourceEdgeFragment.fan_copied_function_copied_app_context_cut
#print axioms Lamping.AG.SourceEdgeFragment.fan_kept_parent_copied_app_context_forward
#print axioms Lamping.AG.SourceEdgeFragment.fan_copied_function_copied_app_context_forward
