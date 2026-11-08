import Lamping.Lamping.FanBodyFragmentTransport
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.lam i j lt) V) site.closed
private abbrev bodyTransportRight (i j : Nat) (lt : i<j) := (Schema.fanAction Op.lam i j lt).right.net
local notation "rhs" => bodyTransportRight i j lt
/-- Low-level complete transport with a synchronized copied BODY writer.
The normalized OLD path is THIS entire real sourcefragment, not parent padding. -/
theorem SourceEdgeFragment.fan_copied_body_kept_reflect
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
    (leftTerminal rightTerminal : NodePort signature K kept)
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftTerminal.1,leftTerminal.2⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightTerminal.1,rightTerminal.2⟩)))
    (pieces : targetFirst.segments=targetSecond.segments) : sourceFirst.segments=sourceSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨leftRaw,_leftOld,ls,_leftSource,leftShape,leftRelation,leftPieceLabels⟩ :=
    sourceFirst.fan_copied_body_kept_cut site flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord leftBranch leftParentAt
      leftTerminal.1 leftTerminal.2 leftEndAt leftLabels
  obtain ⟨rightRaw,_rightOld,rs,_rightSource,rightShape,rightRelation,rightPieceLabels⟩ :=
    sourceSecond.fan_copied_body_kept_cut site flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord rightBranch rightParentAt
      rightTerminal.1 rightTerminal.2 rightEndAt rightLabels
  have maps := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label).invFun) pieces
  dsimp only at maps
  rw [leftShape,rightShape] at maps
  have tails := (List.cons.inj (List.cons.inj (List.cons.inj maps).2).2).2
  exact leftRelation.fixed_source_unique_of_eq site rightRelation (by rw [tails])
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.lam i j lt) V) site.closed
private abbrev fanContextTransportRight (i j : Nat) (lt : i<j) := (Schema.fanAction Op.lam i j lt).right.net
local notation "rhs" => fanContextTransportRight i j lt
theorem SourceEdgeFragment.fan_kept_parent_copied_context_reflect
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {leftEdge rightEdge : SourceEdge} {p q : Path}
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
    (leftBranch rightBranch : Bool)
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftBranch),.inl ()⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightBranch),.inl ()⟩)))
    (pieces : targetFirst.segments=targetSecond.segments) : sourceFirst.segments=sourceSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨lp,leftRaw,leftOld,ls,_leftOldLast,leftNewLast,leftSource,leftShape,leftRelation,leftPieceLabels⟩ :=
    sourceFirst.fan_kept_parent_copied_context_cut site flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord leftParent.1 leftParent.2
      leftParentAt leftBranch leftEndAt leftLabels
  obtain ⟨rp,rightRaw,rightOld,rs,_rightOldLast,rightNewLast,rightSource,rightShape,rightRelation,rightPieceLabels⟩ :=
    sourceSecond.fan_kept_parent_copied_context_cut site flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord rightParent.1 rightParent.2
      rightParentAt rightBranch rightEndAt rightLabels
  have maps := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label).invFun) pieces
  dsimp only at maps
  rw [leftShape,rightShape] at maps
  have last := congrArg List.getLast? maps
  simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or] at last
  have branches : leftBranch=rightBranch := by
    have same := Option.some.inj last
    exact Sum.inl.inj (Sum.inl.inj (Sum.inr.inj (Sum.inr.inj same)))
  subst rightBranch
  have rawSame : leftRaw=rightRaw := List.append_cancel_right maps
  have parents := SourceEdgeFragment.equal_piece_parent_seams targetMatches targetFirst targetSecond
    leftRole rightRole targetLeft targetRight targetLeftWord targetRightWord pieces
  have outsideSame := Option.some.inj (leftNewLast.symm.trans (parents.trans rightNewLast))
  have pivots : lp=rp := by
    apply Sum.inl.inj
    apply (plugEnd (cut).label (rhs).label).injective
    exact outsideSame
  subst rp
  have oldSame := leftRelation.fixed_source_unique_of_eq site rightRelation (by rw [rawSame])
  have oldTails := (List.cons.inj oldSame).2
  rw [leftSource,rightSource,oldTails]
end
end Lamping.AG
#print axioms Lamping.AG.SourceEdgeFragment.fan_copied_body_kept_reflect
#print axioms Lamping.AG.SourceEdgeFragment.fan_kept_parent_copied_context_reflect
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
/-- Target whole representation at actual slots supplies the target equality;
BODY parents and source accesses are recovered from actual occurrences. -/
theorem PathSite.fan_body_copied_parent_same_slot_reflect
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
    (leftTerminal rightTerminal : NodePort signature K kept)
    (leftEndAt : (selection leftPosition).fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftTerminal.1,leftTerminal.2⟩)))
    (rightEndAt : (selection rightPosition).fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightTerminal.1,rightTerminal.2⟩))) :
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
  exact lsource.fan_copied_body_kept_reflect site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget lRole rRole sourceLeft sourceRight leftParent rightParent
    (by rw [sourceLeftWord];exact lSplit) (by rw [sourceRightWord];exact rSplit)
    leftParentWord rightParentWord leftBranch rightBranch leftParentAt rightParentAt
    leftTerminal rightTerminal leftEndAt rightEndAt pieces

/-- The reflected copied-context cell derives its frontier Bool and common
parent pivot from actual piece equality, not from an assumed profile. -/
theorem PathSite.fan_body_kept_parent_same_slot_reflect
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
    (leftParentPort rightParentPort : NodePort signature K kept)
    (leftParentAt : leftParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftParentPort.1,leftParentPort.2⟩)))
    (rightParentAt : rightParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightParentPort.1,rightParentPort.2⟩)))
    (leftBranch rightBranch : Bool)
    (leftEndAt : (selection leftPosition).fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftBranch),.inl ()⟩)))
    (rightEndAt : (selection rightPosition).fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightBranch),.inl ()⟩))) :
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
  exact lsource.fan_kept_parent_copied_context_reflect site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget lRole rRole sourceLeft sourceRight leftParent rightParent
    (by rw [sourceLeftWord];exact lSplit) (by rw [sourceRightWord];exact rSplit)
    leftParentWord rightParentWord leftParentPort rightParentPort leftParentAt rightParentAt
    leftBranch rightBranch leftEndAt rightEndAt pieces
end
end Lamping.AG
#print axioms Lamping.AG.PathSite.fan_body_copied_parent_same_slot_reflect
#print axioms Lamping.AG.PathSite.fan_body_kept_parent_same_slot_reflect
