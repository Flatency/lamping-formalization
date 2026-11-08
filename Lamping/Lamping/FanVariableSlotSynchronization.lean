import Lamping.Lamping.FanCurrentVariableBinders
import Lamping.Lamping.FanLambdaSlotSynchronization
import Lamping.Lambda.PrerequisiteEdgeOrder
namespace Lamping.Lambda.Labelled
/-- A variable FUNCTION read in an actual successful chain forces its real
lexical binder as the next ordinal. The variable jump itself reads no edge. -/
theorem PrerequisiteChain.variable_next_slot {n : Nat}
    (chain : PrerequisiteChain current start edges)
    (slot : edges[n]?=some leaf)
    (atVariable : current.subterm leaf=some (.var stamp index)) :
    ∃ parent rest origin body more,
      leaf=parent++(.body::rest) ∧index=binderDepth rest ∧
      current.subterm parent=some (.lam origin body) ∧
      PrerequisiteChain current parent more ∧
      edges[n+1]?=some parent ∧PrerequisitePrefix current leaf [] parent := by
  obtain ⟨before,after,middle,split,segment,remainder,reads⟩ :=
    chain.split_at_member (List.mem_of_getElem? slot)
  have atSplit : edges[before.length]?=some leaf := by
    rw [split,List.getElem?_append_right (Nat.le_refl _)]
    simp
  obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp slot
  have ordinal : n=before.length := List.getElem?_inj bound chain.nodup (slot.trans atSplit.symm)
  rcases reads with ⟨appStamp,fn,arg,atApp,edgeEq⟩|⟨lamStamp,lamBody,atLam,edgeEq⟩
  · have fnLookup : current.subterm leaf=some fn := by
      rw [edgeEq,LTerm.subterm_append,atApp];simp [LTerm.subterm]
    have fnEq : fn=.var stamp index := Option.some.inj (fnLookup.symm.trans atVariable)
    rcases remainder.app_cases atApp with ⟨l,b,lamEq,_⟩|⟨_,tail,tailEq,tailChain⟩
    · rw [fnEq] at lamEq;cases lamEq
    · have sameLists : leaf::after=leaf::tail := by simpa only [←edgeEq] using tailEq
      have tailEqual := (List.cons.inj sameLists).2
      have leafChain : PrerequisiteChain current leaf after := by
        simpa only [←edgeEq,←tailEqual] using tailChain
      obtain ⟨parent,rest,origin,body,lexical,depth,lookup,next⟩ := leafChain.variable_cases atVariable
      have head : after.head?=some parent := by
        rcases next.lambda_cases lookup with ⟨_,_,_,_,_,equal⟩|⟨_,_,_,_,_,equal,_⟩ <;> rw [equal] <;> rfl
      refine ⟨parent,rest,origin,body,after,lexical,depth,lookup,next,?_,
        .var atVariable lookup lexical depth .refl⟩
      rw [ordinal,split,List.getElem?_append_right (by omega)]
      simpa only [Nat.add_sub_cancel_left,List.getElem?_cons_succ,←List.head?_eq_getElem?] using head
  · rw [←edgeEq] at atLam
    cases Option.some.inj (atVariable.symm.trans atLam)
end Lamping.Lambda.Labelled
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
/-- Variable-slot synchronization follows the internally recovered CURRENT
binder reads at the next ordinal. No next-slot or piece-equality oracle is an input. -/
theorem PathSite.fan_variable_same_slot_branches
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
    (leftTarget rightTarget : RootAccess site.reduce root)
    (leftWord : accessWord site.reduce leftTarget.val=leftPosition.val)
    (rightWord : accessWord site.reduce rightTarget.val=rightPosition.val)
    (leftBranch rightBranch : Bool)
    (leftFinish : leftTarget.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftBranch),lamBind⟩)))
    (rightFinish : rightTarget.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightBranch),lamBind⟩))) :
    leftBranch=rightBranch := by
  obtain ⟨lp,lr,lo,lb,le,ll,ld,lk,lc,ls,_⟩ := first.variable_next_slot leftSlot leftLookup
  obtain ⟨rp,rr,ro,rb,re,rl,rd,rk,rc,rs,_⟩ := second.variable_next_slot rightSlot rightLookup
  let leftBinder : Position current.erase := ⟨lp,by rw [←LTerm.erase_subterm,lk];rfl⟩
  let rightBinder : Position current.erase := ⟨rp,by rw [←LTerm.erase_subterm,rk];rfl⟩
  obtain ⟨leftParent,leftParentWord,_⟩ := Matches.observation site.reduce targetMatches leftBinder
  obtain ⟨rightParent,rightParentWord,_⟩ := Matches.observation site.reduce targetMatches rightBinder
  obtain ⟨a,b,leftLabels⟩ := leftTarget.property.1.1
  obtain ⟨c,d,rightLabels⟩ := rightTarget.property.1.1
  obtain ⟨_,_,_,_,_,_,leftContextFinish,_⟩ := site.fan_current_variable_binder
    targetMatches flow positive oldT leftLookup lk ll ld leftTarget leftParent leftWord leftParentWord
    leftBranch leftFinish leftLabels lc
  obtain ⟨_,_,_,_,_,_,rightContextFinish,_⟩ := site.fan_current_variable_binder
    targetMatches flow positive oldT rightLookup rk rl rd rightTarget rightParent rightWord rightParentWord
    rightBranch rightFinish rightLabels rc
  exact site.fan_lambda_same_slot_branches sourceMatches flow positive principal selection
    first second physical leftBinder rightBinder ls rs leftParent rightParent leftParentWord rightParentWord
    leftBranch rightBranch leftContextFinish rightContextFinish
/-- Explicit source Joint is only an induction hypothesis for obtaining the
source image equality. No actual source Joint truth is asserted. -/
theorem PathSite.fan_variable_joint_same_slot_branches
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
    (leftTarget rightTarget : RootAccess site.reduce root)
    (leftWord : accessWord site.reduce leftTarget.val=leftPosition.val)
    (rightWord : accessWord site.reduce rightTarget.val=rightPosition.val)
    (leftBranch rightBranch : Bool)
    (leftFinish : leftTarget.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftBranch),lamBind⟩)))
    (rightFinish : rightTarget.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightBranch),lamBind⟩))) :
    leftBranch=rightBranch := by
  exact site.fan_variable_same_slot_branches sourceMatches targetMatches flow positive oldT principal
    selection first second ((joint.1 first second).mpr iso) leftPosition rightPosition leftSlot rightSlot
    leftLookup rightLookup leftTarget rightTarget leftWord rightWord leftBranch rightBranch leftFinish rightFinish
end
end Lamping.AG
#print axioms Lamping.Lambda.Labelled.PrerequisiteChain.variable_next_slot
#print axioms Lamping.AG.PathSite.fan_variable_same_slot_branches

#print axioms Lamping.AG.PathSite.fan_variable_joint_same_slot_branches
