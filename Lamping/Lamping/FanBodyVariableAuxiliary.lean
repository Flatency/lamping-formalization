import Lamping.Lamping.FanArgumentVariableAuxiliary
import Lamping.Lamping.FanBodyFragmentTransport
import Lamping.Lamping.FanCopiedBodyBindingCuts
import Lamping.Lamping.FanLambdaMixedSeparation
import Lamping.Lamping.FanLambdaEndpointCases
import Lamping.Lamping.ActionPendingLambdaBranches
set_option maxHeartbeats 4000000
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}
private theorem actual_body_auxiliary
    (lookup : current.subterm edge=some (.var stamp index))
    (body : ∃parent lambdaStamp,edge=parent++[.body] ∧
      current.subterm parent=some (.lam lambdaStamp (.var stamp index))) : AuxiliaryAt current edge := by
  obtain ⟨parent,lambdaStamp,split,_⟩ := body
  constructor
  · rintro ⟨other,a,fn,arg,otherSplit,_⟩
    have last := congrArg List.getLast? (split.symm.trans otherSplit)
    simp at last
  · rintro ⟨a,body,other⟩
    rw [lookup] at other
    cases other
private theorem body_parent (occurrence : OccurrenceFragment current g root leaf)
    (body : ∃parent lambdaStamp,leaf=parent++[.body] ∧
      current.subterm parent=some (.lam lambdaStamp (.var stamp index))) :
    ∃parent lambdaStamp,current.subterm parent=some (.lam lambdaStamp (.var stamp index)) ∧
      leaf=parent++[.body] ∧SourceDeparture (.lam lambdaStamp (.var stamp index)) .body
        (sourceEdge occurrence.environment occurrence.context occurrence.term).fromPort := by
  obtain ⟨parent,a,split,lookup⟩ := body
  obtain ⟨env,ctx,parentOccurrence⟩ := SourceSubterm.of_lookup current lookup [] .external
  have childOccurrence := parentOccurrence.append (SourceSubterm.body SourceSubterm.nil)
  rw [←split] at childOccurrence
  rcases occurrence with ⟨sub,actualEnv,actualCtx,actualOccurrence,fragment⟩
  obtain ⟨rfl,rfl,rfl⟩ := actualOccurrence.same_occurrence childOccurrence
  exact ⟨parent,a,lookup,split,.body⟩
private theorem lambda_first (chain : PrerequisiteChain current p edges)
    (lookup : current.subterm p=some (.lam stamp body)) : edges[0]?=some p := by
  rcases chain.lambda_cases lookup with ⟨_,_,_,_,_,equal⟩|⟨_,_,_,_,_,equal,_⟩ <;> rw [equal] <;> rfl
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
private theorem terminal_mixed_ne
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceFirst : OccurrenceFragment current site.net root p)
    (targetFirst : OccurrenceFragment current site.reduce root p)
    (sourceSecond : OccurrenceFragment current site.net root q)
    (targetSecond : OccurrenceFragment current site.reduce root q)
    (branch : Bool)
    (copyFinish : targetFirst.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),lamBind⟩)))
    (node : K) (port : Port (kept node).sort)
    (keptFinish : targetSecond.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl node,port⟩))) :
    sourceFirst.fragment.segments≠sourceSecond.fragment.segments ∧targetFirst.fragment.segments≠targetSecond.fragment.segments := by
  rcases sourceFirst with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetFirst with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceSecond with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetSecond with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact lsource.fan_lambda_copied_binding_vs_kept_terminal site flow root positive sourceMatches principal
    ltarget rsource rtarget branch copyFinish node port keptFinish

private theorem kept_piece_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {p q : Path}
    (sourceFirst : OccurrenceFragment current site.net root p)
    (targetFirst : OccurrenceFragment current site.reduce root p)
    (sourceSecond : OccurrenceFragment current site.net root q)
    (targetSecond : OccurrenceFragment current site.reduce root q)
    {leftTerm rightTerm : LTerm} {leftStep rightStep : Step}
    (leftRole : SourceDeparture leftTerm leftStep (sourceEdge sourceFirst.environment sourceFirst.context sourceFirst.term).fromPort)
    (rightRole : SourceDeparture rightTerm rightStep (sourceEdge sourceSecond.environment sourceSecond.context sourceSecond.term).fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[leftStep])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[rightStep])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[leftStep])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[rightStep])
    (leftParent rightParent leftEnd rightEnd : NodePort signature K kept)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftParent.1,leftParent.2⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightParent.1,rightParent.2⟩)))
    (leftEndAt : targetFirst.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftEnd.1,leftEnd.2⟩)))
    (rightEndAt : targetSecond.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightEnd.1,rightEnd.2⟩))) :
    targetFirst.fragment.segments=targetSecond.fragment.segments ↔sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  rcases sourceFirst with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetFirst with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceSecond with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetSecond with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact lsource.fan_kept_piece_equality site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget leftRole rightRole sourceLeft sourceRight targetLeft targetRight
    sourceLeftWord sourceRightWord targetLeftWord targetRightWord leftParent rightParent leftEnd rightEnd
    leftParentAt rightParentAt leftEndAt rightEndAt


/-- Real lexical binders from successful endpoint iso, not FUNCTION membership
or a supplied nextslot/profile, synchronize the copied binding endpoints. -/
private theorem endpoint_binding_branches
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root) (principal : SiteActionPrincipal site)
    (closed : Closed current.erase) (selection : OccurrenceFragmentSelection current site.net root)
    (invariant : ChainRepresentationInvariant closed selection)
    (left right : SyntaxIncidence.Edge current)
    (leftLookup : current.subterm left.val=some (.var leftStamp leftIndex))
    (rightLookup : current.subterm right.val=some (.var rightStamp rightIndex))
    (endpoints : SuccessfulEndpointIso current closed (SyntaxIncidence.target current closed left)
      (SyntaxIncidence.target current closed right))
    (leftTarget rightTarget : RootAccess site.reduce root)
    (leftWord : accessWord site.reduce leftTarget.val=left.val)
    (rightWord : accessWord site.reduce rightTarget.val=right.val)
    (leftBranch rightBranch : Bool)
    (leftFinish : leftTarget.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftBranch),lamBind⟩)))
    (rightFinish : rightTarget.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightBranch),lamBind⟩))) :
    leftBranch=rightBranch := by
  obtain ⟨lp,lr,lo,lb,lSplit,lLookup,_lInside,_lErased,lDepth⟩ := current.closed_variable_binder closed leftLookup
  obtain ⟨rp,rr,ro,rb,rSplit,rLookup,_rInside,_rErased,rDepth⟩ := current.closed_variable_binder closed rightLookup
  let leftBinder : Position current.erase := ⟨lp,by rw [←LTerm.erase_subterm,lLookup];rfl⟩
  let rightBinder : Position current.erase := ⟨rp,by rw [←LTerm.erase_subterm,rLookup];rfl⟩
  have leftEndpoint := SyntaxIncidence.target_eq_of_spec current closed left
    (vertex:=some ⟨lp,Or.inr ⟨lo,lb,lLookup⟩⟩) (Or.inr ⟨_,_,_,_,lr,leftLookup,lLookup,lSplit,lDepth⟩)
  have rightEndpoint := SyntaxIncidence.target_eq_of_spec current closed right
    (vertex:=some ⟨rp,Or.inr ⟨ro,rb,rLookup⟩⟩) (Or.inr ⟨_,_,_,_,rr,rightLookup,rLookup,rSplit,rDepth⟩)
  rw [leftEndpoint,rightEndpoint] at endpoints
  obtain ⟨es,fs,first,second,iso⟩ := endpoints
  change PrerequisiteChain current lp es at first
  change PrerequisiteChain current rp fs at second
  have physical := (invariant first second).mpr iso
  obtain ⟨leftParent,leftParentWord,_⟩ := Matches.observation site.reduce targetMatches leftBinder
  obtain ⟨rightParent,rightParentWord,_⟩ := Matches.observation site.reduce targetMatches rightBinder
  obtain ⟨a,b,leftLabels⟩ := leftTarget.property.1.1
  obtain ⟨c,d,rightLabels⟩ := rightTarget.property.1.1
  obtain ⟨_,_,_,_,_,_,leftContextFinish,_⟩ := site.fan_current_variable_binder
    targetMatches flow positive oldT leftLookup lLookup lSplit lDepth leftTarget leftParent leftWord leftParentWord
    leftBranch leftFinish leftLabels first
  obtain ⟨_,_,_,_,_,_,rightContextFinish,_⟩ := site.fan_current_variable_binder
    targetMatches flow positive oldT rightLookup rLookup rSplit rDepth rightTarget rightParent rightWord rightParentWord
    rightBranch rightFinish rightLabels second
  exact site.fan_lambda_same_slot_branches sourceMatches flow positive principal selection first second physical
    leftBinder rightBinder (lambda_first first lLookup) (lambda_first second rLookup)
    leftParent rightParent leftParentWord rightParentWord leftBranch rightBranch leftContextFinish rightContextFinish

private theorem binding_piece_forward
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {p q : Path}
    (sourceFirst : OccurrenceFragment current site.net root p)
    (targetFirst : OccurrenceFragment current site.reduce root p)
    (sourceSecond : OccurrenceFragment current site.net root q)
    (targetSecond : OccurrenceFragment current site.reduce root q)
    (leftRole : SourceDeparture leftTerm leftStep (sourceEdge sourceFirst.environment sourceFirst.context sourceFirst.term).fromPort)
    (rightRole : SourceDeparture rightTerm rightStep (sourceEdge sourceSecond.environment sourceSecond.context sourceSecond.term).fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[leftStep])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[rightStep])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[leftStep])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[rightStep])
    (leftParent rightParent : NodePort signature K kept)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftParent.1,leftParent.2⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightParent.1,rightParent.2⟩)))
    (branch : Bool)
    (leftEndAt : targetFirst.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),lamBind⟩)))
    (rightEndAt : targetSecond.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),lamBind⟩)))
    (pieces : sourceFirst.fragment.segments=sourceSecond.fragment.segments) :
    targetFirst.fragment.segments=targetSecond.fragment.segments := by
  rcases sourceFirst with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetFirst with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceSecond with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetSecond with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact lsource.fan_kept_parent_copied_binding_forward site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget leftRole rightRole sourceLeft sourceRight targetLeft targetRight
    sourceLeftWord sourceRightWord targetLeftWord targetRightWord leftParent rightParent leftParentAt rightParentAt
    branch leftEndAt rightEndAt pieces

private theorem body_kept_forward
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceFirst : OccurrenceFragment current site.net root p)
    (targetFirst : OccurrenceFragment current site.reduce root p)
    (sourceSecond : OccurrenceFragment current site.net root q)
    (targetSecond : OccurrenceFragment current site.reduce root q)
    (leftRole : SourceDeparture leftTerm .body (sourceEdge sourceFirst.environment sourceFirst.context sourceFirst.term).fromPort)
    (rightRole : SourceDeparture rightTerm .body (sourceEdge sourceSecond.environment sourceSecond.context sourceSecond.term).fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[.body])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[.body])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[.body])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[.body])
    (branch : Bool)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)))
    (leftTerminal rightTerminal : NodePort signature K kept)
    (leftEndAt : targetFirst.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftTerminal.1,leftTerminal.2⟩)))
    (rightEndAt : targetSecond.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightTerminal.1,rightTerminal.2⟩)))
    (pieces : sourceFirst.fragment.segments=sourceSecond.fragment.segments) : targetFirst.fragment.segments=targetSecond.fragment.segments := by
  rcases sourceFirst with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetFirst with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceSecond with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetSecond with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact lsource.fan_copied_body_kept_forward site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget leftRole rightRole sourceLeft sourceRight targetLeft targetRight
    sourceLeftWord sourceRightWord targetLeftWord targetRightWord branch leftParentAt rightParentAt
    leftTerminal rightTerminal leftEndAt rightEndAt pieces
private theorem body_binding_forward
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceFirst : OccurrenceFragment current site.net root p)
    (targetFirst : OccurrenceFragment current site.reduce root p)
    (sourceSecond : OccurrenceFragment current site.net root q)
    (targetSecond : OccurrenceFragment current site.reduce root q)
    (leftRole : SourceDeparture leftTerm .body (sourceEdge sourceFirst.environment sourceFirst.context sourceFirst.term).fromPort)
    (rightRole : SourceDeparture rightTerm .body (sourceEdge sourceSecond.environment sourceSecond.context sourceSecond.term).fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[.body])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[.body])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[.body])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[.body])
    (parentBranch childBranch : Bool)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl parentBranch),.inl ()⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl parentBranch),.inl ()⟩)))
    (leftEndAt : targetFirst.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),lamBind⟩)))
    (rightEndAt : targetSecond.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),lamBind⟩)))
    (pieces : sourceFirst.fragment.segments=sourceSecond.fragment.segments) : targetFirst.fragment.segments=targetSecond.fragment.segments := by
  rcases sourceFirst with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetFirst with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceSecond with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetSecond with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact lsource.fan_copied_body_binding_forward site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget leftRole rightRole sourceLeft sourceRight targetLeft targetRight
    sourceLeftWord sourceRightWord targetLeftWord targetRightWord parentBranch childBranch
    leftParentAt rightParentAt leftEndAt rightEndAt pieces
private theorem parent_mixed_ne
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceCopy : OccurrenceFragment current site.net root p)
    (targetCopy : OccurrenceFragment current site.reduce root p)
    (sourceKept : OccurrenceFragment current site.net root q)
    (targetKept : OccurrenceFragment current site.reduce root q)
    (copyRole : SourceDeparture copyTerm .body (sourceEdge sourceCopy.environment sourceCopy.context sourceCopy.term).fromPort)
    (keptRole : SourceDeparture keptTerm keptStep (sourceEdge sourceKept.environment sourceKept.context sourceKept.term).fromPort)
    (sourceCopyParent sourceKeptParent : RootAccess site.net root)
    (targetCopyParent targetKeptParent : RootAccess site.reduce root)
    (sourceCopyWord : p=accessWord site.net sourceCopyParent.val++[.body])
    (sourceKeptWord : q=accessWord site.net sourceKeptParent.val++[keptStep])
    (targetCopyWord : p=accessWord site.reduce targetCopyParent.val++[.body])
    (targetKeptWord : q=accessWord site.reduce targetKeptParent.val++[keptStep])
    (branch : Bool)
    (copyFinish : targetCopyParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)))
    (node : K) (port : Port (kept node).sort)
    (keptFinish : targetKeptParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inl node,port⟩))) :
    sourceCopy.fragment.segments≠sourceKept.fragment.segments ∧targetCopy.fragment.segments≠targetKept.fragment.segments := by
  rcases sourceCopy with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetCopy with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceKept with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetKept with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact lsource.fan_lambda_copied_parent_vs_kept_parent site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget copyRole keptRole sourceCopyParent sourceKeptParent targetCopyParent targetKeptParent
    sourceCopyWord sourceKeptWord targetCopyWord targetKeptWord branch copyFinish node port keptFinish
private theorem endpoint_parent_branches
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site)
    (closed : Closed current.erase) (selection : OccurrenceFragmentSelection current site.net root)
    (joint : JointRepresentation closed selection)
    (left right : SyntaxIncidence.Edge current)
    (leftBody : ∃parent stamp,left.val=parent++[.body] ∧current.subterm parent=some (.lam stamp (.var leftStamp leftIndex)))
    (rightBody : ∃parent stamp,right.val=parent++[.body] ∧current.subterm parent=some (.lam stamp (.var rightStamp rightIndex)))
    (endpoints : SuccessfulEndpointIso current closed (SyntaxIncidence.source current left) (SyntaxIncidence.source current right))
    (leftTarget rightTarget : RootAccess site.reduce root)
    (leftWord : left.val=accessWord site.reduce leftTarget.val++[.body])
    (rightWord : right.val=accessWord site.reduce rightTarget.val++[.body])
    (leftBranch rightBranch : Bool)
    (leftFinish : leftTarget.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftBranch),.inl ()⟩)))
    (rightFinish : rightTarget.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightBranch),.inl ()⟩))) : leftBranch=rightBranch := by
  obtain ⟨lp,la,lSplit,lLookup⟩ := leftBody
  obtain ⟨rp,ra,rSplit,rLookup⟩ := rightBody
  have leftEndpoint := SyntaxIncidence.source_eq_of_spec current left
    (vertex:=some ⟨lp,Or.inr ⟨_,_,lLookup⟩⟩) ⟨.body,_,_,lSplit,lLookup,.body⟩
  have rightEndpoint := SyntaxIncidence.source_eq_of_spec current right
    (vertex:=some ⟨rp,Or.inr ⟨_,_,rLookup⟩⟩) ⟨.body,_,_,rSplit,rLookup,.body⟩
  rw [leftEndpoint,rightEndpoint] at endpoints
  obtain ⟨es,fs,first,second,iso⟩ := endpoints
  change PrerequisiteChain current lp es at first
  change PrerequisiteChain current rp fs at second
  exact site.prerequisite_lambda_copy_branches sourceMatches flow positive principal closed selection joint
    lLookup rLookup first second iso leftTarget rightTarget
    (List.append_cancel_right (leftWord.symm.trans lSplit))
    (List.append_cancel_right (rightWord.symm.trans rSplit)) leftBranch rightBranch leftFinish rightFinish
/-- Natural BODY-variable endpoint equality. SOURCE Aux, actual metadata
and both independent copied Bool families are all derived internally. -/
theorem PathSite.fan_body_variable_endpoint_equality
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root) (principal : SiteActionPrincipal site)
    (closed : Closed current.erase)
    (source : OccurrenceFragmentSelection current site.net root)
    (target : OccurrenceFragmentSelection current site.reduce root)
    (sourceJoint : JointRepresentation closed source)
    (left right : SyntaxIncidence.Edge current)
    (leftLookup : current.subterm left.val=some (.var leftStamp leftIndex))
    (rightLookup : current.subterm right.val=some (.var rightStamp rightIndex))
    (leftBody : ∃parent stamp,left.val=parent++[.body] ∧current.subterm parent=some (.lam stamp (.var leftStamp leftIndex)))
    (rightBody : ∃parent stamp,right.val=parent++[.body] ∧current.subterm parent=some (.lam stamp (.var rightStamp rightIndex)))
    (sameLabel : SyntaxIncidence.label current left=SyntaxIncidence.label current right)
    (sourceIso : SuccessfulEndpointIso current closed (SyntaxIncidence.source current left) (SyntaxIncidence.source current right))
    (targetIso : SuccessfulEndpointIso current closed (SyntaxIncidence.target current closed left) (SyntaxIncidence.target current closed right)) :
    (target left).fragment.segments=(target right).fragment.segments := by
  have pieces : (source left).fragment.segments=(source right).fragment.segments := by
    apply Classical.byContradiction
    intro different
    exact (sourceJoint.2 left right (actual_body_auxiliary leftLookup leftBody)
      (actual_body_auxiliary rightLookup rightBody) sameLabel different) ⟨sourceIso,targetIso⟩
  let sourceFirst := source left
  let sourceSecond := source right
  let targetFirst := target left
  let targetSecond := target right
  obtain ⟨lp,la,lLookup,lSplit,lRole⟩ := body_parent sourceFirst leftBody
  obtain ⟨rp,ra,rLookup,rSplit,rRole⟩ := body_parent sourceSecond rightBody
  let leftParentPosition : Position current.erase := ⟨lp,by rw [←LTerm.erase_subterm,lLookup];rfl⟩
  let rightParentPosition : Position current.erase := ⟨rp,by rw [←LTerm.erase_subterm,rLookup];rfl⟩
  obtain ⟨sourceLeft,sourceLeftWord,_⟩ := Matches.observation site.net sourceMatches leftParentPosition
  obtain ⟨sourceRight,sourceRightWord,_⟩ := Matches.observation site.net sourceMatches rightParentPosition
  obtain ⟨targetLeft,targetLeftWord,_⟩ := Matches.observation site.reduce targetMatches leftParentPosition
  obtain ⟨targetRight,targetRightWord,_⟩ := Matches.observation site.reduce targetMatches rightParentPosition
  have slWord : left.val=accessWord site.net sourceLeft.val++[.body] := by rw [sourceLeftWord];exact lSplit
  have srWord : right.val=accessWord site.net sourceRight.val++[.body] := by rw [sourceRightWord];exact rSplit
  have tlWord : left.val=accessWord site.reduce targetLeft.val++[.body] := by rw [targetLeftWord];exact lSplit
  have trWord : right.val=accessWord site.reduce targetRight.val++[.body] := by rw [targetRightWord];exact rSplit
  have lKind := targetMatches.variable_access_typed leftLookup targetFirst.fragment.access targetFirst.fragment.word
  have rKind := targetMatches.variable_access_typed rightLookup targetSecond.fragment.access targetSecond.fragment.word
  rcases site.fan_lambda_access_cases targetLeft (targetMatches.lambda_access_typed lLookup targetLeft targetLeftWord) with
    ⟨lpPort,lpAt⟩|⟨lpBool,lpAt⟩
  · rcases site.fan_lambda_access_cases targetRight (targetMatches.lambda_access_typed rLookup targetRight targetRightWord) with
      ⟨rpPort,rpAt⟩|⟨rpBool,rpAt⟩
    · rcases site.fan_variable_access_cases targetFirst.fragment.access lKind with ⟨lcPort,lcAt⟩|⟨lcBool,lcAt⟩
      · rcases site.fan_variable_access_cases targetSecond.fragment.access rKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
        · exact (kept_piece_equality site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond
            lRole rRole sourceLeft sourceRight targetLeft targetRight slWord srWord tlWord trWord
            lpPort rpPort lcPort rcPort lpAt rpAt lcAt rcAt).mpr pieces
        · exact False.elim ((terminal_mixed_ne site flow root positive sourceMatches principal sourceSecond targetSecond sourceFirst targetFirst
            rcBool rcAt lcPort.1 lcPort.2 lcAt).1 pieces.symm)
      · rcases site.fan_variable_access_cases targetSecond.fragment.access rKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
        · exact False.elim ((terminal_mixed_ne site flow root positive sourceMatches principal sourceFirst targetFirst sourceSecond targetSecond
            lcBool lcAt rcPort.1 rcPort.2 rcAt).1 pieces)
        · have branches := endpoint_binding_branches site sourceMatches targetMatches flow positive oldT principal closed source sourceJoint.1
            left right leftLookup rightLookup targetIso targetFirst.fragment.access targetSecond.fragment.access
            targetFirst.fragment.word targetSecond.fragment.word lcBool rcBool lcAt rcAt
          subst rcBool
          exact binding_piece_forward site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond
            lRole rRole sourceLeft sourceRight targetLeft targetRight slWord srWord tlWord trWord lpPort rpPort lpAt rpAt lcBool lcAt rcAt pieces
    · exact False.elim ((parent_mixed_ne site flow root positive sourceMatches targetMatches principal sourceSecond targetSecond sourceFirst targetFirst
        rRole lRole sourceRight sourceLeft targetRight targetLeft srWord slWord trWord tlWord rpBool rpAt lpPort.1 lpPort.2 lpAt).1 pieces.symm)
  · rcases site.fan_lambda_access_cases targetRight (targetMatches.lambda_access_typed rLookup targetRight targetRightWord) with
      ⟨rpPort,rpAt⟩|⟨rpBool,rpAt⟩
    · exact False.elim ((parent_mixed_ne site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond
        lRole rRole sourceLeft sourceRight targetLeft targetRight slWord srWord tlWord trWord lpBool lpAt rpPort.1 rpPort.2 rpAt).1 pieces)
    · have parentBranches := endpoint_parent_branches site sourceMatches flow positive principal closed source sourceJoint
        left right leftBody rightBody sourceIso targetLeft targetRight tlWord trWord lpBool rpBool lpAt rpAt
      subst rpBool
      rcases site.fan_variable_access_cases targetFirst.fragment.access lKind with ⟨lcPort,lcAt⟩|⟨lcBool,lcAt⟩
      · rcases site.fan_variable_access_cases targetSecond.fragment.access rKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
        · exact body_kept_forward site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond
            lRole rRole sourceLeft sourceRight targetLeft targetRight slWord srWord tlWord trWord lpBool lpAt rpAt lcPort rcPort lcAt rcAt pieces
        · exact False.elim ((terminal_mixed_ne site flow root positive sourceMatches principal sourceSecond targetSecond sourceFirst targetFirst
            rcBool rcAt lcPort.1 lcPort.2 lcAt).1 pieces.symm)
      · rcases site.fan_variable_access_cases targetSecond.fragment.access rKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
        · exact False.elim ((terminal_mixed_ne site flow root positive sourceMatches principal sourceFirst targetFirst sourceSecond targetSecond
            lcBool lcAt rcPort.1 rcPort.2 rcAt).1 pieces)
        · have branches := endpoint_binding_branches site sourceMatches targetMatches flow positive oldT principal closed source sourceJoint.1
            left right leftLookup rightLookup targetIso targetFirst.fragment.access targetSecond.fragment.access
            targetFirst.fragment.word targetSecond.fragment.word lcBool rcBool lcAt rcAt
          subst rcBool
          exact body_binding_forward site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond
            lRole rRole sourceLeft sourceRight targetLeft targetRight slWord srWord tlWord trWord lpBool lcBool lpAt rpAt lcAt rcAt pieces
/-- The genuine BODY-variable restricted D017 consequence, not all Aux or Joint. -/
theorem PathSite.fan_body_variable_auxiliary_separation
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root) (principal : SiteActionPrincipal site)
    (closed : Closed current.erase)
    (source : OccurrenceFragmentSelection current site.net root)
    (target : OccurrenceFragmentSelection current site.reduce root)
    (sourceJoint : JointRepresentation closed source)
    (left right : SyntaxIncidence.Edge current)
    (leftLookup : current.subterm left.val=some (.var leftStamp leftIndex))
    (rightLookup : current.subterm right.val=some (.var rightStamp rightIndex))
    (leftBody : ∃parent stamp,left.val=parent++[.body] ∧current.subterm parent=some (.lam stamp (.var leftStamp leftIndex)))
    (rightBody : ∃parent stamp,right.val=parent++[.body] ∧current.subterm parent=some (.lam stamp (.var rightStamp rightIndex)))
    (sameLabel : SyntaxIncidence.label current left=SyntaxIncidence.label current right)
    (different : (target left).fragment.segments≠(target right).fragment.segments) :
    ¬(SuccessfulEndpointIso current closed (SyntaxIncidence.source current left) (SyntaxIncidence.source current right) ∧
      SuccessfulEndpointIso current closed (SyntaxIncidence.target current closed left) (SyntaxIncidence.target current closed right)) := by
  rintro ⟨sourceIso,targetIso⟩
  exact different (site.fan_body_variable_endpoint_equality sourceMatches targetMatches flow positive oldT principal closed
    source target sourceJoint left right leftLookup rightLookup leftBody rightBody sameLabel sourceIso targetIso)
end
end Lamping.AG
#print axioms Lamping.AG.PathSite.fan_body_variable_endpoint_equality
#print axioms Lamping.AG.PathSite.fan_body_variable_auxiliary_separation
