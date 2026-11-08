import Lamping.Lamping.FanCopiedBindingCuts
import Lamping.Lamping.ActualFragmentFanUniqueness
import Lamping.Lamping.FanVariableSlotSynchronization
import Lamping.Lamping.ActionSyntaxObservationKinds
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.lam i j lt) V) site.closed
private abbrev fanVariableRight (i j : Nat) (lt : i<j) := (Schema.fanAction Op.lam i j lt).right.net
local notation "rhs" => fanVariableRight i j lt
/-- Forward equality after a genuine kept-parent cut and SAME copied binding
Bool. Fan raw uniqueness is the actual-source NoPassive theorem, not unary uniqueness. -/
theorem SourceEdgeFragment.fan_kept_parent_copied_binding_forward
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
    (branch : Bool)
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),lamBind⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),lamBind⟩)))
    (pieces : sourceFirst.segments=sourceSecond.segments) : targetFirst.segments=targetSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨lp,leftRaw,ls,lo,leftOldLast,_leftNewLast,leftShape,leftRelation,leftPieceLabels⟩ :=
    sourceFirst.fan_kept_parent_copied_binding_cut site flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord leftParent.1 leftParent.2
      leftParentAt branch leftEndAt leftLabels
  obtain ⟨rp,rightRaw,rs,ro,rightOldLast,_rightNewLast,rightShape,rightRelation,rightPieceLabels⟩ :=
    sourceSecond.fan_kept_parent_copied_binding_cut site flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord rightParent.1 rightParent.2
      rightParentAt branch rightEndAt rightLabels
  have parents := SourceEdgeFragment.equal_piece_parent_seams sourceMatches sourceFirst sourceSecond
    leftRole rightRole sourceLeft sourceRight sourceLeftWord sourceRightWord pieces
  have outsideSame := Option.some.inj (leftOldLast.symm.trans (parents.trans rightOldLast))
  have pivots : lp=rp := by
    apply Sum.inl.inj
    apply (fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition (Schema.fanAction .lam i j lt) V)).symm.injective
    exact outsideSame
  subst rp
  obtain ⟨parentInput,parentOutput,parentLabels⟩ := targetLeft.property.1.1
  have parentWord : accessWord site.net sourceLeft.val=accessWord site.reduce targetLeft.val :=
    List.append_cancel_right (sourceLeftWord.symm.trans targetLeftWord)
  obtain ⟨_,_,parentFinish⟩ := site.action_kept_canonical_access (.fan .lam i j lt) flow root positive
    sourceMatches principal sourceLeft targetLeft parentWord leftParent.1 leftParent.2 leftParentAt parentLabels
  rw [←pieces] at rightRelation
  obtain ⟨_,rawSame⟩ := sourceFirst.fan_target_unique_of_kept_parent_fragment site sourceMatches leftRole
    sourceLeft sourceLeftWord leftParent.1 leftParent.2 parentFinish lp leftOldLast
    leftRelation rightRelation leftPieceLabels rightPieceLabels
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
/-- The actual successful slot supplies its APP parent and original departure
port even when the occurrence carries repeated labels. -/
theorem OccurrenceFragment.variable_function_parent
    {n : Nat} (occurrence : OccurrenceFragment current g root leaf)
    (chain : PrerequisiteChain current start edges) (slot : edges[n]?=some leaf)
    (atVariable : current.subterm leaf=some (.var stamp index)) :
    ∃ parent appStamp arg,current.subterm parent=some (.app appStamp (.var stamp index) arg) ∧
      leaf=parent++[.fn] ∧
      SourceDeparture (.app appStamp (.var stamp index) arg) .fn
        (sourceEdge occurrence.environment occurrence.context occurrence.term).fromPort := by
  obtain ⟨_,_,middle,_,_,_,reads⟩ := chain.split_at_member (List.mem_of_getElem? slot)
  rcases reads with ⟨a,fn,arg,atApp,edgeEq⟩|⟨l,body,atLam,edgeEq⟩
  · have fnLookup : current.subterm leaf=some fn := by
      rw [edgeEq,LTerm.subterm_append,atApp];simp [LTerm.subterm]
    have fnEq : fn=.var stamp index := Option.some.inj (fnLookup.symm.trans atVariable)
    subst fn
    obtain ⟨env,ctx,parentOccurrence⟩ := SourceSubterm.of_lookup current atApp [] .external
    have childOccurrence := parentOccurrence.append (SourceSubterm.fn SourceSubterm.nil)
    rw [←edgeEq] at childOccurrence
    rcases occurrence with ⟨sub,actualEnv,actualCtx,actualOccurrence,fragment⟩
    obtain ⟨rfl,rfl,rfl⟩ := actualOccurrence.same_occurrence childOccurrence
    exact ⟨middle,a,arg,atApp,edgeEq,.fn⟩
  · rw [←edgeEq] at atLam
    cases Option.some.inj (atVariable.symm.trans atLam)
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
/-- A corresponding successful variable slot transports its complete physical
fragment forward. Both APP parents, their kept endpoints, the OLD piece and
copied binding Bool are derived, rather than supplied as branch/piece profiles. -/
theorem PathSite.fan_variable_same_slot_fragment_forward
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root) (principal : SiteActionPrincipal site)
    (selection : OccurrenceFragmentSelection current site.net root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (leftLookup : current.subterm leftPosition.val=some (.var leftStamp leftIndex))
    (rightLookup : current.subterm rightPosition.val=some (.var rightStamp rightIndex))
    (targetFirst : OccurrenceFragment current site.reduce root leftPosition.val)
    (targetSecond : OccurrenceFragment current site.reduce root rightPosition.val)
    (leftBranch rightBranch : Bool)
    (leftFinish : targetFirst.fragment.access.val.getLast?=
      some (site.reduce.wire (.inl ⟨.inr (.inl leftBranch),lamBind⟩)))
    (rightFinish : targetSecond.fragment.access.val.getLast?=
      some (site.reduce.wire (.inl ⟨.inr (.inl rightBranch),lamBind⟩))) :
    targetFirst.fragment.segments=targetSecond.fragment.segments := by
  have pieces := same_chain_representation_slot selection first second physical leftPosition rightPosition leftSlot rightSlot
  have branches := site.fan_variable_same_slot_branches sourceMatches targetMatches flow positive oldT principal
    selection first second physical leftPosition rightPosition leftSlot rightSlot leftLookup rightLookup
    targetFirst.fragment.access targetSecond.fragment.access targetFirst.fragment.word targetSecond.fragment.word
    leftBranch rightBranch leftFinish rightFinish
  subst rightBranch
  obtain ⟨lp,la,larg,lLookup,lSplit,lRole⟩ :=
    (selection leftPosition).variable_function_parent first leftSlot leftLookup
  obtain ⟨rp,ra,rarg,rLookup,rSplit,rRole⟩ :=
    (selection rightPosition).variable_function_parent second rightSlot rightLookup
  let leftParentPosition : Position current.erase := ⟨lp,by rw [←LTerm.erase_subterm,lLookup];rfl⟩
  let rightParentPosition : Position current.erase := ⟨rp,by rw [←LTerm.erase_subterm,rLookup];rfl⟩
  obtain ⟨sourceLeft,sourceLeftWord,_⟩ := Matches.observation site.net sourceMatches leftParentPosition
  obtain ⟨sourceRight,sourceRightWord,_⟩ := Matches.observation site.net sourceMatches rightParentPosition
  obtain ⟨targetLeft,targetLeftWord,lu,leftShape,leftObs⟩ := Matches.observation site.reduce targetMatches leftParentPosition
  obtain ⟨targetRight,targetRightWord,ru,rightShape,rightObs⟩ := Matches.observation site.reduce targetMatches rightParentPosition
  have lErased : subtermAt current.erase lp=some (.app (.var leftIndex) larg.erase) := by
    rw [←LTerm.erase_subterm,lLookup];rfl
  have rErased : subtermAt current.erase rp=some (.app (.var rightIndex) rarg.erase) := by
    rw [←LTerm.erase_subterm,rLookup];rfl
  have leftTerm : lu=.app (.var leftIndex) larg.erase := Option.some.inj (leftShape.symm.trans lErased)
  have rightTerm : ru=.app (.var rightIndex) rarg.erase := Option.some.inj (rightShape.symm.trans rErased)
  subst lu
  subst ru
  have excluded : ∀port : Port (.op .lam),portKind (.op .lam) port≠some AccessKind.app := by
    intro port wrong
    rcases port with u|b
    · cases u;cases wrong
    · cases b <;> cases wrong
  obtain ⟨leftParent,leftParentAt⟩ := site.action_access_kept_of_kind_excluded (.fan .lam i j lt)
    targetLeft leftObs.1 excluded
  obtain ⟨rightParent,rightParentAt⟩ := site.action_access_kept_of_kind_excluded (.fan .lam i j lt)
    targetRight rightObs.1 excluded
  generalize lSourceEq : selection leftPosition=sourceFirst at pieces lRole
  generalize rSourceEq : selection rightPosition=sourceSecond at pieces rRole
  rcases sourceFirst with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetFirst with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceSecond with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetSecond with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact lsource.fan_kept_parent_copied_binding_forward site flow root positive sourceMatches targetMatches
    principal ltarget rsource rtarget lRole rRole sourceLeft sourceRight targetLeft targetRight
    (by rw [sourceLeftWord];exact lSplit) (by rw [sourceRightWord];exact rSplit)
    (by rw [targetLeftWord];exact lSplit) (by rw [targetRightWord];exact rSplit)
    leftParent rightParent leftParentAt rightParentAt leftBranch leftFinish rightFinish pieces

/-- Source Joint may supply the source equality through a genuine chain iso.
It is an explicit induction hypothesis, not actual Joint truth or target REP. -/
theorem PathSite.fan_variable_joint_same_slot_fragment_forward
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root) (principal : SiteActionPrincipal site)
    (closed : Closed current.erase) (selection : OccurrenceFragmentSelection current site.net root)
    (joint : JointRepresentation closed selection)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (iso : ChainIncidenceIsomorphic (chainSyntaxIncidence current closed left)
      (chainSyntaxIncidence current closed right))
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (leftLookup : current.subterm leftPosition.val=some (.var leftStamp leftIndex))
    (rightLookup : current.subterm rightPosition.val=some (.var rightStamp rightIndex))
    (targetFirst : OccurrenceFragment current site.reduce root leftPosition.val)
    (targetSecond : OccurrenceFragment current site.reduce root rightPosition.val)
    (leftBranch rightBranch : Bool)
    (leftFinish : targetFirst.fragment.access.val.getLast?=
      some (site.reduce.wire (.inl ⟨.inr (.inl leftBranch),lamBind⟩)))
    (rightFinish : targetSecond.fragment.access.val.getLast?=
      some (site.reduce.wire (.inl ⟨.inr (.inl rightBranch),lamBind⟩))) :
    targetFirst.fragment.segments=targetSecond.fragment.segments := by
  exact site.fan_variable_same_slot_fragment_forward sourceMatches targetMatches flow positive oldT principal
    selection first second ((joint.1 first second).mpr iso) leftPosition rightPosition leftSlot rightSlot
    leftLookup rightLookup targetFirst targetSecond leftBranch rightBranch leftFinish rightFinish
end
end Lamping.AG
#print axioms Lamping.AG.SourceEdgeFragment.fan_kept_parent_copied_binding_forward
#print axioms Lamping.AG.OccurrenceFragment.variable_function_parent
#print axioms Lamping.AG.PathSite.fan_variable_same_slot_fragment_forward
#print axioms Lamping.AG.PathSite.fan_variable_joint_same_slot_fragment_forward
