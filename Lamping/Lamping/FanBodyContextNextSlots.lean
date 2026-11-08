import Lamping.Lamping.FanLambdaSlotSynchronization
import Lamping.Lambda.PrerequisiteEdgeOrder
namespace Lamping.Lambda.Labelled
/-- A true BODY-parent occurrence is anchored by its actual SourceSubterm. -/
private theorem body_parent
    (occurrence : SourceSubterm [] .external current leaf env ctx sub)
    (incoming : ∃stamp,ctx=.lamBody stamp) :
    ∃ parent stamp body,leaf=parent++[.body] ∧current.subterm parent=some (.lam stamp body) := by
  rcases occurrence.last_departure with ⟨_,external⟩|⟨parent,step,term,split,lookup,role⟩
  · rcases incoming with ⟨stamp,equal⟩;cases external.symm.trans equal
  · cases role with
    | fn => rcases incoming with ⟨stamp,equal⟩;cases equal
    | arg => rcases incoming with ⟨stamp,equal⟩;cases equal
    | body => exact ⟨parent,_,_,split,lookup⟩

private theorem no_function_body_end {p q : Path} : p++[.fn]≠q++[.body] := by
  intro same
  have ends := congrArg List.getLast? same
  simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or] at ends
  cases ends

/-- BODY lambda-context reading consumes its actual edge before reaching its
actual parent lambda. The next ordinal is derived, never given by the caller. -/
theorem PrerequisiteChain.body_context_next_slot {n : Nat}
    (chain : PrerequisiteChain current start edges)
    (slot : edges[n]?=some leaf)
    (atLambda : current.subterm leaf=some (.lam childStamp childBody))
    (occurrence : SourceSubterm [] .external current leaf env ctx sub)
    (incoming : ∃stamp,ctx=.lamBody stamp) :
    ∃ parent stamp body more,leaf=parent++[.body] ∧
      current.subterm parent=some (.lam stamp body) ∧PrerequisiteChain current parent more ∧
      edges[n+1]?=some parent ∧PrerequisitePrefix current leaf [leaf] parent := by
  obtain ⟨parent,stamp,body,lexical,parentLookup⟩ := body_parent occurrence incoming
  obtain ⟨before,after,middle,split,_segment,remainder,reads⟩ :=
    chain.split_at_member (List.mem_of_getElem? slot)
  have atSplit : edges[before.length]?=some leaf := by
    rw [split,List.getElem?_append_right (Nat.le_refl _)];simp
  obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp slot
  have ordinal : n=before.length := List.getElem?_inj bound chain.nodup (slot.trans atSplit.symm)
  rcases reads with ⟨_,_,_,_,edgeEq⟩|⟨_,_,_,edgeEq⟩
  · exact False.elim (no_function_body_end (edgeEq.symm.trans lexical))
  · rw [←edgeEq] at remainder
    rcases remainder.lambda_cases atLambda with ⟨otherParent,_,_,atFunction,_,_⟩|
      ⟨otherParent,step,tail,atParent,_notFunction,listEq,parentChain⟩
    · exact False.elim (no_function_body_end (atFunction.symm.trans lexical))
    · have steps : step=.body := by
        have ends := congrArg List.getLast? (atParent.symm.trans lexical)
        simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or] at ends
        exact Option.some.inj ends
      subst step
      have parents : otherParent=parent := List.append_cancel_right (atParent.symm.trans lexical)
      have tailEq : after=tail := (List.cons.inj listEq).2
      rw [parents,←tailEq] at parentChain
      have head : after.head?=some parent := by
        rcases parentChain.lambda_cases parentLookup with ⟨_,_,_,_,_,equal⟩|⟨_,_,_,_,_,equal,_⟩ <;> rw [equal] <;> rfl
      have segment : PrerequisitePrefix current leaf [leaf] parent := by
        rw [lexical] at atLambda ⊢
        exact .lam atLambda (by decide) .refl
      refine ⟨parent,stamp,body,after,lexical,parentLookup,parentChain,?_,segment⟩
      rw [ordinal,split,List.getElem?_append_right (by omega)]
      simpa only [Nat.add_sub_cancel_left,List.getElem?_cons_succ,←List.head?_eq_getElem?] using head
end Lamping.Lambda.Labelled
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
/-- Conditional adjacent-slot synchronization. The parent coordinate and next
ordinal are internal; parent RootAccess word and copied endpoints are actual
geometric cases, not an assumed branch profile or a branch equality. -/
theorem PathSite.fan_body_context_adjacent_branches
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (matching : Matches site.net root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site)
    (selection : OccurrenceFragmentSelection current site.net root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (leftLookup : current.subterm leftPosition.val=some (.lam leftStamp leftBody))
    (rightLookup : current.subterm rightPosition.val=some (.lam rightStamp rightBody))
    (leftIncoming : ∃stamp,(selection leftPosition).context=.lamBody stamp)
    (rightIncoming : ∃stamp,(selection rightPosition).context=.lamBody stamp)
    (leftChild rightChild leftParent rightParent : RootAccess site.reduce root)
    (leftWord : accessWord site.reduce leftChild.val=leftPosition.val)
    (rightWord : accessWord site.reduce rightChild.val=rightPosition.val)
    (leftParentWord : leftPosition.val=accessWord site.reduce leftParent.val++[.body])
    (rightParentWord : rightPosition.val=accessWord site.reduce rightParent.val++[.body])
    (leftChildBool rightChildBool leftParentBool rightParentBool : Bool)
    (leftChildFinish : leftChild.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftChildBool),.inl ()⟩)))
    (rightChildFinish : rightChild.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightChildBool),.inl ()⟩)))
    (leftParentFinish : leftParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftParentBool),.inl ()⟩)))
    (rightParentFinish : rightParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightParentBool),.inl ()⟩))) :
    leftChildBool=rightChildBool ∧leftParentBool=rightParentBool := by
  obtain ⟨lp,lo,lb,le,lSplit,lLookup,_lc,lNext,_lPrefix⟩ := first.body_context_next_slot leftSlot leftLookup
    (selection leftPosition).occurrence leftIncoming
  obtain ⟨rp,ro,rb,re,rSplit,rLookup,_rc,rNext,_rPrefix⟩ := second.body_context_next_slot rightSlot rightLookup
    (selection rightPosition).occurrence rightIncoming
  let leftParentPosition : Position current.erase := ⟨lp,by rw [←LTerm.erase_subterm,lLookup];rfl⟩
  let rightParentPosition : Position current.erase := ⟨rp,by rw [←LTerm.erase_subterm,rLookup];rfl⟩
  have leftParentActual : accessWord site.reduce leftParent.val=lp :=
    List.append_cancel_right (leftParentWord.symm.trans lSplit)
  have rightParentActual : accessWord site.reduce rightParent.val=rp :=
    List.append_cancel_right (rightParentWord.symm.trans rSplit)
  exact ⟨site.fan_lambda_same_slot_branches matching flow positive principal selection first second physical
      leftPosition rightPosition leftSlot rightSlot leftChild rightChild leftWord rightWord
      leftChildBool rightChildBool leftChildFinish rightChildFinish,
    site.fan_lambda_same_slot_branches matching flow positive principal selection first second physical
      leftParentPosition rightParentPosition lNext rNext leftParent rightParent leftParentActual rightParentActual
      leftParentBool rightParentBool leftParentFinish rightParentFinish⟩

/-- Source Joint supplies only the source whole-image equality, conditionally. -/
theorem PathSite.fan_body_context_joint_adjacent_branches
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (matching : Matches site.net root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site)
    (closed : Closed current.erase) (selection : OccurrenceFragmentSelection current site.net root)
    (joint : JointRepresentation closed selection)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (iso : ChainIncidenceIsomorphic (chainSyntaxIncidence current closed left) (chainSyntaxIncidence current closed right))
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (leftLookup : current.subterm leftPosition.val=some (.lam leftStamp leftBody))
    (rightLookup : current.subterm rightPosition.val=some (.lam rightStamp rightBody))
    (leftIncoming : ∃stamp,(selection leftPosition).context=.lamBody stamp)
    (rightIncoming : ∃stamp,(selection rightPosition).context=.lamBody stamp)
    (leftChild rightChild leftParent rightParent : RootAccess site.reduce root)
    (leftWord : accessWord site.reduce leftChild.val=leftPosition.val)
    (rightWord : accessWord site.reduce rightChild.val=rightPosition.val)
    (leftParentWord : leftPosition.val=accessWord site.reduce leftParent.val++[.body])
    (rightParentWord : rightPosition.val=accessWord site.reduce rightParent.val++[.body])
    (leftChildBool rightChildBool leftParentBool rightParentBool : Bool)
    (leftChildFinish : leftChild.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftChildBool),.inl ()⟩)))
    (rightChildFinish : rightChild.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightChildBool),.inl ()⟩)))
    (leftParentFinish : leftParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftParentBool),.inl ()⟩)))
    (rightParentFinish : rightParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightParentBool),.inl ()⟩))) :
    leftChildBool=rightChildBool ∧leftParentBool=rightParentBool := by
  exact site.fan_body_context_adjacent_branches matching flow positive principal selection first second
    ((joint.1 first second).mpr iso) leftPosition rightPosition leftSlot rightSlot leftLookup rightLookup
    leftIncoming rightIncoming leftChild rightChild leftParent rightParent leftWord rightWord
    leftParentWord rightParentWord leftChildBool rightChildBool leftParentBool rightParentBool
    leftChildFinish rightChildFinish leftParentFinish rightParentFinish
end
end Lamping.AG
#print axioms Lamping.Lambda.Labelled.PrerequisiteChain.body_context_next_slot
#print axioms Lamping.AG.PathSite.fan_body_context_adjacent_branches
#print axioms Lamping.AG.PathSite.fan_body_context_joint_adjacent_branches
