import Lamping.Lamping.FanCopiedBodyKeptCuts
import Lamping.Lamping.FanLambdaContextFragmentTransport
import Lamping.Lamping.FanBodyContextNextSlots
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
theorem SourceEdgeFragment.fan_copied_body_kept_forward
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
    (branch : Bool)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)))
    (leftTerminal rightTerminal : NodePort signature K kept)
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftTerminal.1,leftTerminal.2⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightTerminal.1,rightTerminal.2⟩)))
    (pieces : sourceFirst.segments=sourceSecond.segments) : targetFirst.segments=targetSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨leftRaw,_leftOld,ls,_leftSource,leftShape,leftRelation,leftPieceLabels⟩ :=
    sourceFirst.fan_copied_body_kept_cut site flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord branch leftParentAt
      leftTerminal.1 leftTerminal.2 leftEndAt leftLabels
  obtain ⟨rightRaw,_rightOld,rs,_rightSource,rightShape,rightRelation,rightPieceLabels⟩ :=
    sourceSecond.fan_copied_body_kept_cut site flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord branch rightParentAt
      rightTerminal.1 rightTerminal.2 rightEndAt rightLabels
  have rawSame := sourceFirst.fan_target_unique_of_contiguous_source site leftRelation rightRelation
    leftPieceLabels rightPieceLabels pieces (pre:=[]) (post:=[]) (by simp)
  have tails := (List.cons.inj rawSame).2
  have maps : targetFirst.segments.map (plugEnd (cut).label (rhs).label).invFun=
      targetSecond.segments.map (plugEnd (cut).label (rhs).label).invFun := by
    rw [leftShape,rightShape,tails]
  have physical := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label)) maps
  simpa only [plug_decomposition_flatten] using physical
end
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}
/-- Recover the actual BODY parent's role as well as its literal coordinate. -/
theorem OccurrenceFragment.lambda_body_parent
    (occurrence : OccurrenceFragment current g root leaf)
    (incoming : ∃stamp,occurrence.context=.lamBody stamp) :
    ∃parent stamp body,current.subterm parent=some (.lam stamp body) ∧leaf=parent++[.body] ∧
      SourceDeparture (.lam stamp body) .body
        (sourceEdge occurrence.environment occurrence.context occurrence.term).fromPort := by
  rcases occurrence with ⟨sub,env,ctx,atSite,fragment⟩
  have fromPort : (sourceEdge env ctx sub).fromPort=ctx := by cases sub <;> rfl
  rcases atSite.last_departure with ⟨_,external⟩|⟨parent,step,term,split,lookup,role⟩
  · obtain ⟨stamp,equal⟩ := incoming;cases external.symm.trans equal
  · cases role with
    | fn => obtain ⟨stamp,equal⟩ := incoming;cases equal
    | arg => obtain ⟨stamp,equal⟩ := incoming;cases equal
    | body => exact ⟨parent,_,_,lookup,split,by rw [fromPort];exact .body⟩
end
end Lamping.AG
#print axioms Lamping.AG.SourceEdgeFragment.fan_copied_body_kept_forward
#print axioms Lamping.AG.OccurrenceFragment.lambda_body_parent
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
/-- A successful BODY-lambda slot derives its parent at the next ordinal;
source whole representation synchronizes the writer Bool and OLD piece. -/
theorem PathSite.fan_body_copied_parent_same_slot_forward
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
    (leftTerminal rightTerminal : NodePort signature K kept)
    (leftEndAt : targetFirst.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftTerminal.1,leftTerminal.2⟩)))
    (rightEndAt : targetSecond.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightTerminal.1,rightTerminal.2⟩))) :
    targetFirst.fragment.segments=targetSecond.fragment.segments := by
  have pieces := same_chain_representation_slot selection first second physical leftPosition rightPosition leftSlot rightSlot
  obtain ⟨lp,lo,lb,lLookup,lSplit,lRole⟩ := (selection leftPosition).lambda_body_parent leftIncoming
  obtain ⟨rp,ro,rb,rLookup,rSplit,rRole⟩ := (selection rightPosition).lambda_body_parent rightIncoming
  obtain ⟨lp',_lo',_lb',_more,lSplit',_lookup',_chain,lNext,_prefix⟩ :=
    first.body_context_next_slot leftSlot leftLookup (selection leftPosition).occurrence leftIncoming
  obtain ⟨rp',_ro',_rb',_more',rSplit',_lookup'',_chain',rNext,_prefix'⟩ :=
    second.body_context_next_slot rightSlot rightLookup (selection rightPosition).occurrence rightIncoming
  have lpEq : lp'=lp := List.append_cancel_right (lSplit'.symm.trans lSplit)
  have rpEq : rp'=rp := List.append_cancel_right (rSplit'.symm.trans rSplit)
  rw [lpEq] at lNext
  rw [rpEq] at rNext
  let leftParentPosition : Position current.erase := ⟨lp,by rw [←LTerm.erase_subterm,lLookup];rfl⟩
  let rightParentPosition : Position current.erase := ⟨rp,by rw [←LTerm.erase_subterm,rLookup];rfl⟩
  have leftParentActual : accessWord site.reduce leftParent.val=lp := List.append_cancel_right (leftParentWord.symm.trans lSplit)
  have rightParentActual : accessWord site.reduce rightParent.val=rp := List.append_cancel_right (rightParentWord.symm.trans rSplit)
  have branches := site.fan_lambda_same_slot_branches sourceMatches flow positive principal selection first second
    physical leftParentPosition rightParentPosition lNext rNext leftParent rightParent leftParentActual rightParentActual
    leftBranch rightBranch leftParentAt rightParentAt
  subst rightBranch
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
  exact lsource.fan_copied_body_kept_forward site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget lRole rRole sourceLeft sourceRight leftParent rightParent
    (by rw [sourceLeftWord];exact lSplit) (by rw [sourceRightWord];exact rSplit)
    leftParentWord rightParentWord leftBranch leftParentAt rightParentAt leftTerminal rightTerminal leftEndAt rightEndAt pieces

/-- The kept BODY-parent cell reuses the real contiguous-source fan theorem.
The copied child Bool and OLD block both come from the same source ordinal. -/
theorem PathSite.fan_body_kept_parent_same_slot_forward
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site) (selection : OccurrenceFragmentSelection current site.net root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (leftIncoming : ∃stamp,(selection leftPosition).context=.lamBody stamp)
    (rightIncoming : ∃stamp,(selection rightPosition).context=.lamBody stamp)
    (targetFirst : OccurrenceFragment current site.reduce root leftPosition.val)
    (targetSecond : OccurrenceFragment current site.reduce root rightPosition.val)
    (leftParent rightParent : RootAccess site.reduce root)
    (leftParentWord : leftPosition.val=accessWord site.reduce leftParent.val++[.body])
    (rightParentWord : rightPosition.val=accessWord site.reduce rightParent.val++[.body])
    (leftParentPort rightParentPort : NodePort signature K kept)
    (leftParentAt : leftParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftParentPort.1,leftParentPort.2⟩)))
    (rightParentAt : rightParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightParentPort.1,rightParentPort.2⟩)))
    (leftBranch rightBranch : Bool)
    (leftEndAt : targetFirst.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftBranch),.inl ()⟩)))
    (rightEndAt : targetSecond.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightBranch),.inl ()⟩))) :
    targetFirst.fragment.segments=targetSecond.fragment.segments := by
  have pieces := same_chain_representation_slot selection first second physical leftPosition rightPosition leftSlot rightSlot
  have branches := site.fan_lambda_same_slot_branches sourceMatches flow positive principal selection first second
    physical leftPosition rightPosition leftSlot rightSlot targetFirst.fragment.access targetSecond.fragment.access
    targetFirst.fragment.word targetSecond.fragment.word leftBranch rightBranch leftEndAt rightEndAt
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
  exact lsource.fan_kept_parent_copied_context_forward site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget lRole rRole sourceLeft sourceRight leftParent rightParent
    (by rw [sourceLeftWord];exact lSplit) (by rw [sourceRightWord];exact rSplit)
    leftParentWord rightParentWord leftParentPort rightParentPort leftParentAt rightParentAt
    leftBranch leftEndAt rightEndAt pieces
end
end Lamping.AG
#print axioms Lamping.AG.PathSite.fan_body_copied_parent_same_slot_forward
#print axioms Lamping.AG.PathSite.fan_body_kept_parent_same_slot_forward
