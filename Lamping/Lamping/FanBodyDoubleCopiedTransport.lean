import Lamping.Lamping.FanCopiedLambdaBodyContextCuts
import Lamping.Lamping.FanBodyFragmentReflection
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.lam i j lt) V) site.closed
private abbrev doubleBodyRight (i j : Nat) (lt : i<j) := (Schema.fanAction Op.lam i j lt).right.net
local notation "rhs" => doubleBodyRight i j lt
/-- Complete CC forward transport; normalized OLD is contiguous in THIS source fragment. -/
theorem SourceEdgeFragment.fan_double_copied_body_forward
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
    (parentBranch : Bool)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl parentBranch),.inl ()⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl parentBranch),.inl ()⟩)))
    (childBranch : Bool)
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),.inl ()⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),.inl ()⟩)))
    (pieces : sourceFirst.segments=sourceSecond.segments) : targetFirst.segments=targetSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨leftRaw,leftOld,ls,leftSource,leftShape,leftRelation,leftPieceLabels⟩ :=
    sourceFirst.fan_copied_body_context_cut site flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord parentBranch childBranch leftParentAt leftEndAt leftLabels
  obtain ⟨rightRaw,rightOld,rs,rightSource,rightShape,rightRelation,rightPieceLabels⟩ :=
    sourceSecond.fan_copied_body_context_cut site flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord parentBranch childBranch rightParentAt rightEndAt rightLabels
  have oldSame := List.append_cancel_right (leftSource.symm.trans (pieces.trans rightSource))
  have rawSame := sourceFirst.fan_target_unique_of_contiguous_source site leftRelation rightRelation
    leftPieceLabels rightPieceLabels oldSame (pre:=[]) (post:=principal.edges) (by simpa using leftSource)
  have tails := (List.cons.inj rawSame).2
  have maps : targetFirst.segments.map (plugEnd (cut).label (rhs).label).invFun=
      targetSecond.segments.map (plugEnd (cut).label (rhs).label).invFun := by
    rw [leftShape,rightShape,tails]
  have physical := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label)) maps
  simpa only [plug_decomposition_flatten] using physical

/-- Complete CC reflection derives the frontier Bool from the actual target last slot. -/
theorem SourceEdgeFragment.fan_double_copied_body_reflect
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
    (leftBranch rightBranch : Bool)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftBranch),.inl ()⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightBranch),.inl ()⟩)))
    (leftChildBranch rightChildBranch : Bool)
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftChildBranch),.inl ()⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightChildBranch),.inl ()⟩)))
    (pieces : targetFirst.segments=targetSecond.segments) : sourceFirst.segments=sourceSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨leftRaw,leftOld,ls,leftSource,leftShape,leftRelation,_leftPieceLabels⟩ :=
    sourceFirst.fan_copied_body_context_cut site flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord leftBranch leftChildBranch leftParentAt leftEndAt leftLabels
  obtain ⟨rightRaw,rightOld,rs,rightSource,rightShape,rightRelation,_rightPieceLabels⟩ :=
    sourceSecond.fan_copied_body_context_cut site flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord rightBranch rightChildBranch rightParentAt rightEndAt rightLabels
  have maps := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label).invFun) pieces
  dsimp only at maps
  rw [leftShape,rightShape] at maps
  have tails := (List.cons.inj (List.cons.inj (List.cons.inj maps).2).2).2
  have last := congrArg List.getLast? tails
  simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or] at last
  have branches : leftChildBranch=rightChildBranch := by
    have same := Option.some.inj last
    exact Sum.inl.inj (Sum.inl.inj (Sum.inr.inj (Sum.inr.inj same)))
  subst rightChildBranch
  have rawSame : leftRaw=rightRaw := List.append_cancel_right tails
  have oldSame := leftRelation.fixed_source_unique_of_eq site rightRelation (by rw [rawSame])
  rw [leftSource,rightSource,oldSame]

theorem PathSite.fan_body_double_copied_same_slot_forward
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site) (selection : OccurrenceFragmentSelection current site.net root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (leftLookup : current.subterm leftPosition.val=some (.lam leftStamp leftBody))
    (rightLookup : current.subterm rightPosition.val=some (.lam rightStamp rightBody))
    (leftIncoming : ∃stamp,(selection leftPosition).context=.lamBody stamp)
    (rightIncoming : ∃stamp,(selection rightPosition).context=.lamBody stamp)
    (targetFirst : OccurrenceFragment current site.reduce root leftPosition.val)
    (targetSecond : OccurrenceFragment current site.reduce root rightPosition.val)
    (leftParent rightParent : RootAccess site.reduce root)
    (leftParentWord : leftPosition.val=accessWord site.reduce leftParent.val++[.body])
    (rightParentWord : rightPosition.val=accessWord site.reduce rightParent.val++[.body])
    (leftBranch rightBranch : Bool)
    (leftParentAt : leftParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftBranch),.inl ()⟩)))
    (rightParentAt : rightParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightBranch),.inl ()⟩)))
    (leftChildBranch rightChildBranch : Bool)
    (leftEndAt : (targetFirst).fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftChildBranch),.inl ()⟩)))
    (rightEndAt : (targetSecond).fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightChildBranch),.inl ()⟩))) :
    targetFirst.fragment.segments=targetSecond.fragment.segments := by
  have pieces := same_chain_representation_slot selection first second physical leftPosition rightPosition leftSlot rightSlot
  have branches := site.fan_body_context_adjacent_branches sourceMatches flow positive principal selection
    first second physical leftPosition rightPosition leftSlot rightSlot leftLookup rightLookup leftIncoming rightIncoming
    targetFirst.fragment.access targetSecond.fragment.access leftParent rightParent
    targetFirst.fragment.word targetSecond.fragment.word leftParentWord rightParentWord
    leftChildBranch rightChildBranch leftBranch rightBranch leftEndAt rightEndAt leftParentAt rightParentAt
  obtain ⟨childBranches,parentBranches⟩ := branches
  subst rightChildBranch
  subst rightBranch
  obtain ⟨lp,lo,lb,lLookup,lSplit,lRole⟩ := (selection leftPosition).lambda_body_parent leftIncoming
  obtain ⟨rp,ro,rb,rLookup,rSplit,rRole⟩ := (selection rightPosition).lambda_body_parent rightIncoming
  let leftParentPosition : Position current.erase := ⟨lp,by rw [←LTerm.erase_subterm,lLookup];rfl⟩
  let rightParentPosition : Position current.erase := ⟨rp,by rw [←LTerm.erase_subterm,rLookup];rfl⟩
  obtain ⟨sourceLeft,sourceLeftWord,_⟩ := Matches.observation site.net sourceMatches leftParentPosition
  obtain ⟨sourceRight,sourceRightWord,_⟩ := Matches.observation site.net sourceMatches rightParentPosition
  generalize lSourceEq : selection leftPosition=sourceFirst at pieces lRole
  generalize rSourceEq : selection rightPosition=sourceSecond at pieces rRole
  rcases sourceFirst with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetFirst with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceSecond with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetSecond with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact lsource.fan_double_copied_body_forward site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget lRole rRole sourceLeft sourceRight leftParent rightParent
    (by rw [sourceLeftWord];exact lSplit) (by rw [sourceRightWord];exact rSplit)
    leftParentWord rightParentWord leftBranch leftParentAt rightParentAt leftChildBranch leftEndAt rightEndAt pieces

theorem PathSite.fan_body_double_copied_same_slot_reflect
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site) (selection : OccurrenceFragmentSelection current site.reduce root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (leftIncoming : ∃stamp,(selection leftPosition).context=.lamBody stamp)
    (rightIncoming : ∃stamp,(selection rightPosition).context=.lamBody stamp)
    (sourceFirst : OccurrenceFragment current site.net root leftPosition.val)
    (sourceSecond : OccurrenceFragment current site.net root rightPosition.val)
    (leftParent rightParent : RootAccess site.reduce root)
    (leftParentWord : leftPosition.val=accessWord site.reduce leftParent.val++[.body])
    (rightParentWord : rightPosition.val=accessWord site.reduce rightParent.val++[.body])
    (leftBranch rightBranch : Bool)
    (leftParentAt : leftParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftBranch),.inl ()⟩)))
    (rightParentAt : rightParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightBranch),.inl ()⟩)))
    (leftChildBranch rightChildBranch : Bool)
    (leftEndAt : (selection leftPosition).fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftChildBranch),.inl ()⟩)))
    (rightEndAt : (selection rightPosition).fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightChildBranch),.inl ()⟩))) :
    sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  have pieces := same_chain_representation_slot selection first second physical leftPosition rightPosition leftSlot rightSlot
  obtain ⟨lp,lo,lb,lLookup,lSplit,lRole⟩ := (selection leftPosition).lambda_body_parent leftIncoming
  obtain ⟨rp,ro,rb,rLookup,rSplit,rRole⟩ := (selection rightPosition).lambda_body_parent rightIncoming
  let leftParentPosition : Position current.erase := ⟨lp,by rw [←LTerm.erase_subterm,lLookup];rfl⟩
  let rightParentPosition : Position current.erase := ⟨rp,by rw [←LTerm.erase_subterm,rLookup];rfl⟩
  obtain ⟨sourceLeft,sourceLeftWord,_⟩ := Matches.observation site.net sourceMatches leftParentPosition
  obtain ⟨sourceRight,sourceRightWord,_⟩ := Matches.observation site.net sourceMatches rightParentPosition
  generalize lTargetEq : selection leftPosition=targetFirst at pieces lRole leftEndAt
  generalize rTargetEq : selection rightPosition=targetSecond at pieces rRole rightEndAt
  rcases sourceFirst with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetFirst with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceSecond with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetSecond with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact lsource.fan_double_copied_body_reflect site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget lRole rRole sourceLeft sourceRight leftParent rightParent
    (by rw [sourceLeftWord];exact lSplit) (by rw [sourceRightWord];exact rSplit)
    leftParentWord rightParentWord leftBranch rightBranch leftParentAt rightParentAt leftChildBranch rightChildBranch leftEndAt rightEndAt pieces
end
end Lamping.AG
#print axioms Lamping.AG.SourceEdgeFragment.fan_double_copied_body_forward
#print axioms Lamping.AG.SourceEdgeFragment.fan_double_copied_body_reflect

#print axioms Lamping.AG.PathSite.fan_body_double_copied_same_slot_forward
#print axioms Lamping.AG.PathSite.fan_body_double_copied_same_slot_reflect
