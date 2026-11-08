import Lamping.Lamping.FanBodyDoubleCopiedTransport
import Lamping.Checks.FanBodyFragmentTransportConsumer
namespace Lamping.Checks.FanBodyDoubleCopiedTransportConsumer
open AG Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
/-- Direct conditional CC high consumer, four arbitrary actual selections.
Both representation inputs are explicit conditional hypotheses, not claims of
an inhabited closed CC cell or of actual Joint truth. -/
theorem conditional_cc_four_choices
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site) (selection otherSource : OccurrenceFragmentSelection current site.net root)
    (targetSelection otherTarget : OccurrenceFragmentSelection current site.reduce root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (targetPhysical : SameChainRepresentation targetSelection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (leftLookup : current.subterm leftPosition.val=some (.lam leftStamp leftBody))
    (rightLookup : current.subterm rightPosition.val=some (.lam rightStamp rightBody))
    (leftIncoming : ∃stamp,(selection leftPosition).context=.lamBody stamp)
    (rightIncoming : ∃stamp,(selection rightPosition).context=.lamBody stamp)
    (leftParent rightParent : RootAccess site.reduce root)
    (leftParentWord : leftPosition.val=accessWord site.reduce leftParent.val++[.body])
    (rightParentWord : rightPosition.val=accessWord site.reduce rightParent.val++[.body])
    (leftBranch rightBranch : Bool)
    (leftParentAt : leftParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftBranch),.inl ()⟩)))
    (rightParentAt : rightParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightBranch),.inl ()⟩)))
    (leftChildBranch rightChildBranch : Bool)
    (leftEndAt : (targetSelection leftPosition).fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftChildBranch),.inl ()⟩)))
    (rightEndAt : (otherTarget rightPosition).fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightChildBranch),.inl ()⟩))) :
    (targetSelection leftPosition).fragment.segments=(otherTarget rightPosition).fragment.segments ∧
      (selection leftPosition).fragment.segments=(otherSource rightPosition).fragment.segments := by
  have forward := site.fan_body_double_copied_same_slot_forward sourceMatches targetMatches flow positive principal
    selection first second physical leftPosition rightPosition leftSlot rightSlot leftLookup rightLookup leftIncoming rightIncoming
    (targetSelection leftPosition) (otherTarget rightPosition) leftParent rightParent leftParentWord rightParentWord
    leftBranch rightBranch leftParentAt rightParentAt leftChildBranch rightChildBranch leftEndAt rightEndAt
  have targetLeftIncoming : ∃stamp,(targetSelection leftPosition).context=.lamBody stamp := by
    obtain ⟨stamp,inc⟩ := leftIncoming
    exact ⟨stamp,((targetSelection leftPosition).occurrence.same_occurrence (selection leftPosition).occurrence).2.1.trans inc⟩
  have targetRightIncoming : ∃stamp,(targetSelection rightPosition).context=.lamBody stamp := by
    obtain ⟨stamp,inc⟩ := rightIncoming
    exact ⟨stamp,((targetSelection rightPosition).occurrence.same_occurrence (selection rightPosition).occurrence).2.1.trans inc⟩
  have rightAccess := OccurrenceFragment.access_unique targetMatches (targetSelection rightPosition) (otherTarget rightPosition)
  have rightActual : (targetSelection rightPosition).fragment.access.val.getLast?=some
      (site.reduce.wire (.inl ⟨.inr (.inl rightChildBranch),.inl ()⟩)) := by
    rw [rightAccess];exact rightEndAt
  exact ⟨forward,site.fan_body_double_copied_same_slot_reflect sourceMatches targetMatches flow positive principal
    targetSelection first second targetPhysical leftPosition rightPosition leftSlot rightSlot targetLeftIncoming targetRightIncoming
    (selection leftPosition) (otherSource rightPosition) leftParent rightParent leftParentWord rightParentWord
    leftBranch rightBranch leftParentAt rightParentAt leftChildBranch rightChildBranch leftEndAt rightActual⟩
end
open FanBodyDoubleLambdaReachable FanBodyDoubleLambdaParents
/-- Genuine K serial natural-cell supply remains available and is kept
separate from the conditional SAME-site CC consumer above. -/
theorem existing_k_serial_cells :
    INIT original ∧History [[]] original current ∧Closed original.erase ∧Closed current.erase ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet outerFan.site.reduce)
      [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet innerFan.site.reduce)
      [.beta 0,.fanAction .lam 0 1 (by decide),.fanAction .lam 0 1 (by decide)] ∧
    Nonempty (OccurrenceFragmentSelection current outerFan.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current outerFan.site.reduce (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current innerFan.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current innerFan.site.reduce (.inl ())) := by
  obtain ⟨initial,history,closed,targetClosed,outerTrace,_,_,outerSource,outerTarget,_,_⟩ :=
    FanBodyFragmentTransportConsumer.actual_outer_supply
  obtain ⟨_,_,_,_,innerTrace,_,_,innerSource,innerTarget,_,_⟩ :=
    FanBodyFragmentTransportConsumer.actual_inner_supply
  exact ⟨initial,history,closed,targetClosed,outerTrace,innerTrace,outerSource,outerTarget,innerSource,innerTarget⟩
end Lamping.Checks.FanBodyDoubleCopiedTransportConsumer
#print axioms Lamping.Checks.FanBodyDoubleCopiedTransportConsumer.conditional_cc_four_choices
#print axioms Lamping.Checks.FanBodyDoubleCopiedTransportConsumer.existing_k_serial_cells
#print axioms Lamping.Checks.FanBodyFragmentTransportConsumer.actual_outer_forward
#print axioms Lamping.Checks.FanBodyFragmentTransportConsumer.actual_inner_forward
