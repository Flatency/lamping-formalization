import Lamping.Lamping.FanVariableBindingComparison
import Lamping.Lamping.FanProperSlotDispatcher
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
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

private theorem copied_piece_reflect
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
    (leftBranch rightBranch : Bool)
    (leftEndAt : targetFirst.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftBranch),lamBind⟩)))
    (rightEndAt : targetSecond.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightBranch),lamBind⟩)))
    (pieces : targetFirst.fragment.segments=targetSecond.fragment.segments) : sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  rcases sourceFirst with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetFirst with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceSecond with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetSecond with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact lsource.fan_kept_parent_copied_binding_reflect site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget leftRole rightRole sourceLeft sourceRight targetLeft targetRight
    sourceLeftWord sourceRightWord targetLeftWord targetRightWord leftParent rightParent leftParentAt rightParentAt
    leftBranch rightBranch leftEndAt rightEndAt pieces

theorem PathSite.fan_variable_read_same_slot_forward
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root) (principal : SiteActionPrincipal site) (selection : OccurrenceFragmentSelection current site.net root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (leftLookup : current.subterm leftPosition.val=some (.var leftStamp leftIndex))
    (rightLookup : current.subterm rightPosition.val=some (.var rightStamp rightIndex))
    (targetFirst : OccurrenceFragment current site.reduce root leftPosition.val)
    (targetSecond : OccurrenceFragment current site.reduce root rightPosition.val)
    : targetFirst.fragment.segments=targetSecond.fragment.segments := by
  have pieces := same_chain_representation_slot selection first second physical leftPosition rightPosition leftSlot rightSlot
  let sourceFirst := selection leftPosition
  let sourceSecond := selection rightPosition
  obtain ⟨lp,la,larg,lLookup,lSplit,lRole⟩ := sourceFirst.variable_function_parent first leftSlot leftLookup
  obtain ⟨rp,ra,rarg,rLookup,rSplit,rRole⟩ := sourceSecond.variable_function_parent second rightSlot rightLookup
  let leftParentPosition : Position current.erase := ⟨lp,by rw [←LTerm.erase_subterm,lLookup];rfl⟩
  let rightParentPosition : Position current.erase := ⟨rp,by rw [←LTerm.erase_subterm,rLookup];rfl⟩
  obtain ⟨sourceLeft,sourceLeftWord,_⟩ := Matches.observation site.net sourceMatches leftParentPosition
  obtain ⟨sourceRight,sourceRightWord,_⟩ := Matches.observation site.net sourceMatches rightParentPosition
  obtain ⟨targetLeft,targetLeftWord,_⟩ := Matches.observation site.reduce targetMatches leftParentPosition
  obtain ⟨targetRight,targetRightWord,_⟩ := Matches.observation site.reduce targetMatches rightParentPosition
  have leftParentKind := targetMatches.app_access_typed lLookup targetLeft targetLeftWord
  have rightParentKind := targetMatches.app_access_typed rLookup targetRight targetRightWord
  have excluded : ∀port : Port (.op .lam),portKind (.op .lam) port≠some AccessKind.app := by
    intro port wrong
    rcases port with u|aux
    · cases u;cases wrong
    · cases aux <;> cases wrong
  obtain ⟨lpPort,lpAt⟩ := site.action_access_kept_of_kind_excluded (.fan .lam i j lt) targetLeft leftParentKind excluded
  obtain ⟨rpPort,rpAt⟩ := site.action_access_kept_of_kind_excluded (.fan .lam i j lt) targetRight rightParentKind excluded
  have sourceLeftChildWord : leftPosition.val=accessWord site.net sourceLeft.val++[.fn] := by rw [sourceLeftWord];exact lSplit
  have sourceRightChildWord : rightPosition.val=accessWord site.net sourceRight.val++[.fn] := by rw [sourceRightWord];exact rSplit
  have targetLeftChildWord : leftPosition.val=accessWord site.reduce targetLeft.val++[.fn] := by rw [targetLeftWord];exact lSplit
  have targetRightChildWord : rightPosition.val=accessWord site.reduce targetRight.val++[.fn] := by rw [targetRightWord];exact rSplit
  have leftChildKind := targetMatches.variable_access_typed leftLookup targetFirst.fragment.access targetFirst.fragment.word
  have rightChildKind := targetMatches.variable_access_typed rightLookup targetSecond.fragment.access targetSecond.fragment.word
  rcases site.fan_variable_access_cases targetFirst.fragment.access leftChildKind with ⟨lcPort,lcAt⟩|⟨lcBool,lcAt⟩
  · rcases site.fan_variable_access_cases targetSecond.fragment.access rightChildKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
    · exact (kept_piece_equality site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond lRole rRole sourceLeft sourceRight targetLeft targetRight sourceLeftChildWord sourceRightChildWord targetLeftChildWord targetRightChildWord lpPort rpPort lcPort rcPort lpAt rpAt lcAt rcAt).mpr pieces
    · exact False.elim ((terminal_mixed_ne site flow root positive sourceMatches principal sourceSecond targetSecond sourceFirst targetFirst rcBool rcAt lcPort.1 lcPort.2 lcAt).1 pieces.symm)
  · rcases site.fan_variable_access_cases targetSecond.fragment.access rightChildKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
    · exact False.elim ((terminal_mixed_ne site flow root positive sourceMatches principal sourceFirst targetFirst sourceSecond targetSecond lcBool lcAt rcPort.1 rcPort.2 rcAt).1 pieces)
    · exact site.fan_variable_same_slot_fragment_forward sourceMatches targetMatches flow positive oldT principal
        selection first second physical leftPosition rightPosition leftSlot rightSlot leftLookup rightLookup
        targetFirst targetSecond lcBool rcBool lcAt rcAt

theorem PathSite.fan_variable_read_same_slot_reflect
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site) (selection : OccurrenceFragmentSelection current site.reduce root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (leftLookup : current.subterm leftPosition.val=some (.var leftStamp leftIndex))
    (rightLookup : current.subterm rightPosition.val=some (.var rightStamp rightIndex))
    (sourceFirst : OccurrenceFragment current site.net root leftPosition.val)
    (sourceSecond : OccurrenceFragment current site.net root rightPosition.val)
    : sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  have pieces := same_chain_representation_slot selection first second physical leftPosition rightPosition leftSlot rightSlot
  let targetFirst := selection leftPosition
  let targetSecond := selection rightPosition
  obtain ⟨lp,la,larg,lLookup,lSplit,lRole⟩ := sourceFirst.variable_function_parent first leftSlot leftLookup
  obtain ⟨rp,ra,rarg,rLookup,rSplit,rRole⟩ := sourceSecond.variable_function_parent second rightSlot rightLookup
  let leftParentPosition : Position current.erase := ⟨lp,by rw [←LTerm.erase_subterm,lLookup];rfl⟩
  let rightParentPosition : Position current.erase := ⟨rp,by rw [←LTerm.erase_subterm,rLookup];rfl⟩
  obtain ⟨sourceLeft,sourceLeftWord,_⟩ := Matches.observation site.net sourceMatches leftParentPosition
  obtain ⟨sourceRight,sourceRightWord,_⟩ := Matches.observation site.net sourceMatches rightParentPosition
  obtain ⟨targetLeft,targetLeftWord,_⟩ := Matches.observation site.reduce targetMatches leftParentPosition
  obtain ⟨targetRight,targetRightWord,_⟩ := Matches.observation site.reduce targetMatches rightParentPosition
  have leftParentKind := targetMatches.app_access_typed lLookup targetLeft targetLeftWord
  have rightParentKind := targetMatches.app_access_typed rLookup targetRight targetRightWord
  have excluded : ∀port : Port (.op .lam),portKind (.op .lam) port≠some AccessKind.app := by
    intro port wrong
    rcases port with u|aux
    · cases u;cases wrong
    · cases aux <;> cases wrong
  obtain ⟨lpPort,lpAt⟩ := site.action_access_kept_of_kind_excluded (.fan .lam i j lt) targetLeft leftParentKind excluded
  obtain ⟨rpPort,rpAt⟩ := site.action_access_kept_of_kind_excluded (.fan .lam i j lt) targetRight rightParentKind excluded
  have sourceLeftChildWord : leftPosition.val=accessWord site.net sourceLeft.val++[.fn] := by rw [sourceLeftWord];exact lSplit
  have sourceRightChildWord : rightPosition.val=accessWord site.net sourceRight.val++[.fn] := by rw [sourceRightWord];exact rSplit
  have targetLeftChildWord : leftPosition.val=accessWord site.reduce targetLeft.val++[.fn] := by rw [targetLeftWord];exact lSplit
  have targetRightChildWord : rightPosition.val=accessWord site.reduce targetRight.val++[.fn] := by rw [targetRightWord];exact rSplit
  have leftChildKind := targetMatches.variable_access_typed leftLookup targetFirst.fragment.access targetFirst.fragment.word
  have rightChildKind := targetMatches.variable_access_typed rightLookup targetSecond.fragment.access targetSecond.fragment.word
  rcases site.fan_variable_access_cases targetFirst.fragment.access leftChildKind with ⟨lcPort,lcAt⟩|⟨lcBool,lcAt⟩
  · rcases site.fan_variable_access_cases targetSecond.fragment.access rightChildKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
    · exact (kept_piece_equality site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond lRole rRole sourceLeft sourceRight targetLeft targetRight sourceLeftChildWord sourceRightChildWord targetLeftChildWord targetRightChildWord lpPort rpPort lcPort rcPort lpAt rpAt lcAt rcAt).mp pieces
    · exact False.elim ((terminal_mixed_ne site flow root positive sourceMatches principal sourceSecond targetSecond sourceFirst targetFirst rcBool rcAt lcPort.1 lcPort.2 lcAt).2 pieces.symm)
  · rcases site.fan_variable_access_cases targetSecond.fragment.access rightChildKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
    · exact False.elim ((terminal_mixed_ne site flow root positive sourceMatches principal sourceFirst targetFirst sourceSecond targetSecond lcBool lcAt rcPort.1 rcPort.2 rcAt).2 pieces)
    · exact copied_piece_reflect site flow root positive sourceMatches targetMatches principal
        sourceFirst targetFirst sourceSecond targetSecond lRole rRole sourceLeft sourceRight targetLeft targetRight
        sourceLeftChildWord sourceRightChildWord targetLeftChildWord targetRightChildWord lpPort rpPort lpAt rpAt
        lcBool rcBool lcAt rcAt pieces

end
end Lamping.AG
#print axioms Lamping.AG.PathSite.fan_variable_read_same_slot_forward
#print axioms Lamping.AG.PathSite.fan_variable_read_same_slot_reflect
