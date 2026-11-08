import Lamping.Lamping.FanLambdaEndpointCases
import Lamping.Lamping.FanBodyDoubleCopiedTransport
import Lamping.Lamping.FanLambdaMixedSeparation
import Lamping.Lamping.FanKeptFragmentComparison
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
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

private theorem terminal_mixed_ne
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceCopy : OccurrenceFragment current site.net root p)
    (targetCopy : OccurrenceFragment current site.reduce root p)
    (sourceKept : OccurrenceFragment current site.net root q)
    (targetKept : OccurrenceFragment current site.reduce root q)
    (branch : Bool)
    (copyFinish : targetCopy.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)))
    (node : K) (port : Port (kept node).sort)
    (keptFinish : targetKept.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl node,port⟩))) :
    sourceCopy.fragment.segments≠sourceKept.fragment.segments ∧targetCopy.fragment.segments≠targetKept.fragment.segments := by
  rcases sourceCopy with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetCopy with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceKept with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetKept with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact lsource.fan_lambda_copied_context_vs_kept_terminal site flow root positive sourceMatches principal
    ltarget rsource rtarget branch copyFinish node port keptFinish

private theorem kept_piece_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {p q : Path}
    (sourceCopy : OccurrenceFragment current site.net root p)
    (targetCopy : OccurrenceFragment current site.reduce root p)
    (sourceKept : OccurrenceFragment current site.net root q)
    (targetKept : OccurrenceFragment current site.reduce root q)
    {leftTerm rightTerm : LTerm} {leftStep rightStep : Step}
    (leftRole : SourceDeparture leftTerm leftStep (sourceEdge sourceCopy.environment sourceCopy.context sourceCopy.term).fromPort)
    (rightRole : SourceDeparture rightTerm rightStep (sourceEdge sourceKept.environment sourceKept.context sourceKept.term).fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[leftStep])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[rightStep])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[leftStep])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[rightStep])
    (leftParent rightParent leftEnd rightEnd : NodePort signature K kept)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftParent.1,leftParent.2⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightParent.1,rightParent.2⟩)))
    (leftEndAt : targetCopy.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftEnd.1,leftEnd.2⟩)))
    (rightEndAt : targetKept.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightEnd.1,rightEnd.2⟩))) :
    targetCopy.fragment.segments=targetKept.fragment.segments ↔sourceCopy.fragment.segments=sourceKept.fragment.segments := by
  rcases sourceCopy with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetCopy with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceKept with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetKept with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact lsource.fan_kept_piece_equality site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget leftRole rightRole sourceLeft sourceRight targetLeft targetRight
    sourceLeftWord sourceRightWord targetLeftWord targetRightWord leftParent rightParent leftEnd rightEnd
    leftParentAt rightParentAt leftEndAt rightEndAt

theorem PathSite.fan_body_lambda_same_slot_forward
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
    : targetFirst.fragment.segments=targetSecond.fragment.segments := by
  have pieces := same_chain_representation_slot selection first second physical leftPosition rightPosition leftSlot rightSlot
  let sourceFirst := selection leftPosition
  let sourceSecond := selection rightPosition
  have sourceLeftIncoming : ∃stamp,sourceFirst.context=.lamBody stamp := leftIncoming
  have sourceRightIncoming : ∃stamp,sourceSecond.context=.lamBody stamp := rightIncoming
  obtain ⟨lp,lo,lb,lLookup,lSplit,lRole⟩ := sourceFirst.lambda_body_parent sourceLeftIncoming
  obtain ⟨rp,ro,rb,rLookup,rSplit,rRole⟩ := sourceSecond.lambda_body_parent sourceRightIncoming
  let leftParentPosition : Position current.erase := ⟨lp,by rw [←LTerm.erase_subterm,lLookup];rfl⟩
  let rightParentPosition : Position current.erase := ⟨rp,by rw [←LTerm.erase_subterm,rLookup];rfl⟩
  obtain ⟨sourceLeft,sourceLeftWord,_⟩ := Matches.observation site.net sourceMatches leftParentPosition
  obtain ⟨sourceRight,sourceRightWord,_⟩ := Matches.observation site.net sourceMatches rightParentPosition
  obtain ⟨targetLeft,targetLeftWord,_⟩ := Matches.observation site.reduce targetMatches leftParentPosition
  obtain ⟨targetRight,targetRightWord,_⟩ := Matches.observation site.reduce targetMatches rightParentPosition
  have sourceLeftChildWord : leftPosition.val=accessWord site.net sourceLeft.val++[.body] := by rw [sourceLeftWord];exact lSplit
  have sourceRightChildWord : rightPosition.val=accessWord site.net sourceRight.val++[.body] := by rw [sourceRightWord];exact rSplit
  have targetLeftChildWord : leftPosition.val=accessWord site.reduce targetLeft.val++[.body] := by rw [targetLeftWord];exact lSplit
  have targetRightChildWord : rightPosition.val=accessWord site.reduce targetRight.val++[.body] := by rw [targetRightWord];exact rSplit
  have leftParentKind := targetMatches.lambda_access_typed lLookup targetLeft targetLeftWord
  have rightParentKind := targetMatches.lambda_access_typed rLookup targetRight targetRightWord
  have leftChildKind := targetMatches.lambda_access_typed leftLookup targetFirst.fragment.access targetFirst.fragment.word
  have rightChildKind := targetMatches.lambda_access_typed rightLookup targetSecond.fragment.access targetSecond.fragment.word
  rcases site.fan_lambda_access_cases targetLeft leftParentKind with ⟨lpPort,lpAt⟩|⟨lpBool,lpAt⟩
  · rcases site.fan_lambda_access_cases targetRight rightParentKind with ⟨rpPort,rpAt⟩|⟨rpBool,rpAt⟩
    · rcases site.fan_lambda_access_cases targetFirst.fragment.access leftChildKind with ⟨lcPort,lcAt⟩|⟨lcBool,lcAt⟩
      · rcases site.fan_lambda_access_cases targetSecond.fragment.access rightChildKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
        · exact (kept_piece_equality site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond lRole rRole sourceLeft sourceRight targetLeft targetRight sourceLeftChildWord sourceRightChildWord targetLeftChildWord targetRightChildWord lpPort rpPort lcPort rcPort lpAt rpAt lcAt rcAt).mpr pieces
        · exact False.elim ((terminal_mixed_ne site flow root positive sourceMatches principal sourceSecond targetSecond sourceFirst targetFirst rcBool rcAt lcPort.1 lcPort.2 lcAt).1 pieces.symm)
      · rcases site.fan_lambda_access_cases targetSecond.fragment.access rightChildKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
        · exact False.elim ((terminal_mixed_ne site flow root positive sourceMatches principal sourceFirst targetFirst sourceSecond targetSecond lcBool lcAt rcPort.1 rcPort.2 rcAt).1 pieces)
        · exact site.fan_body_kept_parent_same_slot_forward sourceMatches targetMatches flow positive principal selection first second physical leftPosition rightPosition leftSlot rightSlot leftIncoming rightIncoming targetFirst targetSecond targetLeft targetRight targetLeftChildWord targetRightChildWord lpPort rpPort lpAt rpAt lcBool rcBool lcAt rcAt
    · rcases site.fan_lambda_access_cases targetFirst.fragment.access leftChildKind with ⟨lcPort,lcAt⟩|⟨lcBool,lcAt⟩
      · rcases site.fan_lambda_access_cases targetSecond.fragment.access rightChildKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
        · exact False.elim ((parent_mixed_ne site flow root positive sourceMatches targetMatches principal sourceSecond targetSecond sourceFirst targetFirst rRole lRole sourceRight sourceLeft targetRight targetLeft sourceRightChildWord sourceLeftChildWord targetRightChildWord targetLeftChildWord rpBool rpAt lpPort.1 lpPort.2 lpAt).1 pieces.symm)
        · exact False.elim ((parent_mixed_ne site flow root positive sourceMatches targetMatches principal sourceSecond targetSecond sourceFirst targetFirst rRole lRole sourceRight sourceLeft targetRight targetLeft sourceRightChildWord sourceLeftChildWord targetRightChildWord targetLeftChildWord rpBool rpAt lpPort.1 lpPort.2 lpAt).1 pieces.symm)
      · rcases site.fan_lambda_access_cases targetSecond.fragment.access rightChildKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
        · exact False.elim ((parent_mixed_ne site flow root positive sourceMatches targetMatches principal sourceSecond targetSecond sourceFirst targetFirst rRole lRole sourceRight sourceLeft targetRight targetLeft sourceRightChildWord sourceLeftChildWord targetRightChildWord targetLeftChildWord rpBool rpAt lpPort.1 lpPort.2 lpAt).1 pieces.symm)
        · exact False.elim ((parent_mixed_ne site flow root positive sourceMatches targetMatches principal sourceSecond targetSecond sourceFirst targetFirst rRole lRole sourceRight sourceLeft targetRight targetLeft sourceRightChildWord sourceLeftChildWord targetRightChildWord targetLeftChildWord rpBool rpAt lpPort.1 lpPort.2 lpAt).1 pieces.symm)
  · rcases site.fan_lambda_access_cases targetRight rightParentKind with ⟨rpPort,rpAt⟩|⟨rpBool,rpAt⟩
    · rcases site.fan_lambda_access_cases targetFirst.fragment.access leftChildKind with ⟨lcPort,lcAt⟩|⟨lcBool,lcAt⟩
      · rcases site.fan_lambda_access_cases targetSecond.fragment.access rightChildKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
        · exact False.elim ((parent_mixed_ne site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond lRole rRole sourceLeft sourceRight targetLeft targetRight sourceLeftChildWord sourceRightChildWord targetLeftChildWord targetRightChildWord lpBool lpAt rpPort.1 rpPort.2 rpAt).1 pieces)
        · exact False.elim ((parent_mixed_ne site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond lRole rRole sourceLeft sourceRight targetLeft targetRight sourceLeftChildWord sourceRightChildWord targetLeftChildWord targetRightChildWord lpBool lpAt rpPort.1 rpPort.2 rpAt).1 pieces)
      · rcases site.fan_lambda_access_cases targetSecond.fragment.access rightChildKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
        · exact False.elim ((parent_mixed_ne site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond lRole rRole sourceLeft sourceRight targetLeft targetRight sourceLeftChildWord sourceRightChildWord targetLeftChildWord targetRightChildWord lpBool lpAt rpPort.1 rpPort.2 rpAt).1 pieces)
        · exact False.elim ((parent_mixed_ne site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond lRole rRole sourceLeft sourceRight targetLeft targetRight sourceLeftChildWord sourceRightChildWord targetLeftChildWord targetRightChildWord lpBool lpAt rpPort.1 rpPort.2 rpAt).1 pieces)
    · rcases site.fan_lambda_access_cases targetFirst.fragment.access leftChildKind with ⟨lcPort,lcAt⟩|⟨lcBool,lcAt⟩
      · rcases site.fan_lambda_access_cases targetSecond.fragment.access rightChildKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
        · exact site.fan_body_copied_parent_same_slot_forward sourceMatches targetMatches flow positive principal selection first second physical leftPosition rightPosition leftSlot rightSlot leftLookup rightLookup leftIncoming rightIncoming targetFirst targetSecond targetLeft targetRight targetLeftChildWord targetRightChildWord lpBool rpBool lpAt rpAt lcPort rcPort lcAt rcAt
        · exact False.elim ((terminal_mixed_ne site flow root positive sourceMatches principal sourceSecond targetSecond sourceFirst targetFirst rcBool rcAt lcPort.1 lcPort.2 lcAt).1 pieces.symm)
      · rcases site.fan_lambda_access_cases targetSecond.fragment.access rightChildKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
        · exact False.elim ((terminal_mixed_ne site flow root positive sourceMatches principal sourceFirst targetFirst sourceSecond targetSecond lcBool lcAt rcPort.1 rcPort.2 rcAt).1 pieces)
        · exact site.fan_body_double_copied_same_slot_forward sourceMatches targetMatches flow positive principal selection first second physical leftPosition rightPosition leftSlot rightSlot leftLookup rightLookup leftIncoming rightIncoming targetFirst targetSecond targetLeft targetRight targetLeftChildWord targetRightChildWord lpBool rpBool lpAt rpAt lcBool rcBool lcAt rcAt

theorem PathSite.fan_body_lambda_same_slot_reflect
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site) (selection : OccurrenceFragmentSelection current site.reduce root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (leftLookup : current.subterm leftPosition.val=some (.lam leftStamp leftBody))
    (rightLookup : current.subterm rightPosition.val=some (.lam rightStamp rightBody))
    (leftIncoming : ∃stamp,(selection leftPosition).context=.lamBody stamp)
    (rightIncoming : ∃stamp,(selection rightPosition).context=.lamBody stamp)
    (sourceFirst : OccurrenceFragment current site.net root leftPosition.val)
    (sourceSecond : OccurrenceFragment current site.net root rightPosition.val)
    : sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  have pieces := same_chain_representation_slot selection first second physical leftPosition rightPosition leftSlot rightSlot
  let targetFirst := selection leftPosition
  let targetSecond := selection rightPosition
  have sourceLeftIncoming : ∃stamp,sourceFirst.context=.lamBody stamp := by
    obtain ⟨stamp,inc⟩ := leftIncoming
    exact ⟨stamp,(sourceFirst.occurrence.same_occurrence targetFirst.occurrence).2.1.trans inc⟩
  have sourceRightIncoming : ∃stamp,sourceSecond.context=.lamBody stamp := by
    obtain ⟨stamp,inc⟩ := rightIncoming
    exact ⟨stamp,(sourceSecond.occurrence.same_occurrence targetSecond.occurrence).2.1.trans inc⟩
  obtain ⟨lp,lo,lb,lLookup,lSplit,lRole⟩ := sourceFirst.lambda_body_parent sourceLeftIncoming
  obtain ⟨rp,ro,rb,rLookup,rSplit,rRole⟩ := sourceSecond.lambda_body_parent sourceRightIncoming
  let leftParentPosition : Position current.erase := ⟨lp,by rw [←LTerm.erase_subterm,lLookup];rfl⟩
  let rightParentPosition : Position current.erase := ⟨rp,by rw [←LTerm.erase_subterm,rLookup];rfl⟩
  obtain ⟨sourceLeft,sourceLeftWord,_⟩ := Matches.observation site.net sourceMatches leftParentPosition
  obtain ⟨sourceRight,sourceRightWord,_⟩ := Matches.observation site.net sourceMatches rightParentPosition
  obtain ⟨targetLeft,targetLeftWord,_⟩ := Matches.observation site.reduce targetMatches leftParentPosition
  obtain ⟨targetRight,targetRightWord,_⟩ := Matches.observation site.reduce targetMatches rightParentPosition
  have sourceLeftChildWord : leftPosition.val=accessWord site.net sourceLeft.val++[.body] := by rw [sourceLeftWord];exact lSplit
  have sourceRightChildWord : rightPosition.val=accessWord site.net sourceRight.val++[.body] := by rw [sourceRightWord];exact rSplit
  have targetLeftChildWord : leftPosition.val=accessWord site.reduce targetLeft.val++[.body] := by rw [targetLeftWord];exact lSplit
  have targetRightChildWord : rightPosition.val=accessWord site.reduce targetRight.val++[.body] := by rw [targetRightWord];exact rSplit
  have leftParentKind := targetMatches.lambda_access_typed lLookup targetLeft targetLeftWord
  have rightParentKind := targetMatches.lambda_access_typed rLookup targetRight targetRightWord
  have leftChildKind := targetMatches.lambda_access_typed leftLookup targetFirst.fragment.access targetFirst.fragment.word
  have rightChildKind := targetMatches.lambda_access_typed rightLookup targetSecond.fragment.access targetSecond.fragment.word
  rcases site.fan_lambda_access_cases targetLeft leftParentKind with ⟨lpPort,lpAt⟩|⟨lpBool,lpAt⟩
  · rcases site.fan_lambda_access_cases targetRight rightParentKind with ⟨rpPort,rpAt⟩|⟨rpBool,rpAt⟩
    · rcases site.fan_lambda_access_cases targetFirst.fragment.access leftChildKind with ⟨lcPort,lcAt⟩|⟨lcBool,lcAt⟩
      · rcases site.fan_lambda_access_cases targetSecond.fragment.access rightChildKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
        · exact (kept_piece_equality site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond lRole rRole sourceLeft sourceRight targetLeft targetRight sourceLeftChildWord sourceRightChildWord targetLeftChildWord targetRightChildWord lpPort rpPort lcPort rcPort lpAt rpAt lcAt rcAt).mp pieces
        · exact False.elim ((terminal_mixed_ne site flow root positive sourceMatches principal sourceSecond targetSecond sourceFirst targetFirst rcBool rcAt lcPort.1 lcPort.2 lcAt).2 pieces.symm)
      · rcases site.fan_lambda_access_cases targetSecond.fragment.access rightChildKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
        · exact False.elim ((terminal_mixed_ne site flow root positive sourceMatches principal sourceFirst targetFirst sourceSecond targetSecond lcBool lcAt rcPort.1 rcPort.2 rcAt).2 pieces)
        · exact site.fan_body_kept_parent_same_slot_reflect sourceMatches targetMatches flow positive principal selection first second physical leftPosition rightPosition leftSlot rightSlot leftIncoming rightIncoming sourceFirst sourceSecond targetLeft targetRight targetLeftChildWord targetRightChildWord lpPort rpPort lpAt rpAt lcBool rcBool lcAt rcAt
    · rcases site.fan_lambda_access_cases targetFirst.fragment.access leftChildKind with ⟨lcPort,lcAt⟩|⟨lcBool,lcAt⟩
      · rcases site.fan_lambda_access_cases targetSecond.fragment.access rightChildKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
        · exact False.elim ((parent_mixed_ne site flow root positive sourceMatches targetMatches principal sourceSecond targetSecond sourceFirst targetFirst rRole lRole sourceRight sourceLeft targetRight targetLeft sourceRightChildWord sourceLeftChildWord targetRightChildWord targetLeftChildWord rpBool rpAt lpPort.1 lpPort.2 lpAt).2 pieces.symm)
        · exact False.elim ((parent_mixed_ne site flow root positive sourceMatches targetMatches principal sourceSecond targetSecond sourceFirst targetFirst rRole lRole sourceRight sourceLeft targetRight targetLeft sourceRightChildWord sourceLeftChildWord targetRightChildWord targetLeftChildWord rpBool rpAt lpPort.1 lpPort.2 lpAt).2 pieces.symm)
      · rcases site.fan_lambda_access_cases targetSecond.fragment.access rightChildKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
        · exact False.elim ((parent_mixed_ne site flow root positive sourceMatches targetMatches principal sourceSecond targetSecond sourceFirst targetFirst rRole lRole sourceRight sourceLeft targetRight targetLeft sourceRightChildWord sourceLeftChildWord targetRightChildWord targetLeftChildWord rpBool rpAt lpPort.1 lpPort.2 lpAt).2 pieces.symm)
        · exact False.elim ((parent_mixed_ne site flow root positive sourceMatches targetMatches principal sourceSecond targetSecond sourceFirst targetFirst rRole lRole sourceRight sourceLeft targetRight targetLeft sourceRightChildWord sourceLeftChildWord targetRightChildWord targetLeftChildWord rpBool rpAt lpPort.1 lpPort.2 lpAt).2 pieces.symm)
  · rcases site.fan_lambda_access_cases targetRight rightParentKind with ⟨rpPort,rpAt⟩|⟨rpBool,rpAt⟩
    · rcases site.fan_lambda_access_cases targetFirst.fragment.access leftChildKind with ⟨lcPort,lcAt⟩|⟨lcBool,lcAt⟩
      · rcases site.fan_lambda_access_cases targetSecond.fragment.access rightChildKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
        · exact False.elim ((parent_mixed_ne site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond lRole rRole sourceLeft sourceRight targetLeft targetRight sourceLeftChildWord sourceRightChildWord targetLeftChildWord targetRightChildWord lpBool lpAt rpPort.1 rpPort.2 rpAt).2 pieces)
        · exact False.elim ((parent_mixed_ne site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond lRole rRole sourceLeft sourceRight targetLeft targetRight sourceLeftChildWord sourceRightChildWord targetLeftChildWord targetRightChildWord lpBool lpAt rpPort.1 rpPort.2 rpAt).2 pieces)
      · rcases site.fan_lambda_access_cases targetSecond.fragment.access rightChildKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
        · exact False.elim ((parent_mixed_ne site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond lRole rRole sourceLeft sourceRight targetLeft targetRight sourceLeftChildWord sourceRightChildWord targetLeftChildWord targetRightChildWord lpBool lpAt rpPort.1 rpPort.2 rpAt).2 pieces)
        · exact False.elim ((parent_mixed_ne site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond lRole rRole sourceLeft sourceRight targetLeft targetRight sourceLeftChildWord sourceRightChildWord targetLeftChildWord targetRightChildWord lpBool lpAt rpPort.1 rpPort.2 rpAt).2 pieces)
    · rcases site.fan_lambda_access_cases targetFirst.fragment.access leftChildKind with ⟨lcPort,lcAt⟩|⟨lcBool,lcAt⟩
      · rcases site.fan_lambda_access_cases targetSecond.fragment.access rightChildKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
        · exact site.fan_body_copied_parent_same_slot_reflect sourceMatches targetMatches flow positive principal selection first second physical leftPosition rightPosition leftSlot rightSlot leftIncoming rightIncoming sourceFirst sourceSecond targetLeft targetRight targetLeftChildWord targetRightChildWord lpBool rpBool lpAt rpAt lcPort rcPort lcAt rcAt
        · exact False.elim ((terminal_mixed_ne site flow root positive sourceMatches principal sourceSecond targetSecond sourceFirst targetFirst rcBool rcAt lcPort.1 lcPort.2 lcAt).2 pieces.symm)
      · rcases site.fan_lambda_access_cases targetSecond.fragment.access rightChildKind with ⟨rcPort,rcAt⟩|⟨rcBool,rcAt⟩
        · exact False.elim ((terminal_mixed_ne site flow root positive sourceMatches principal sourceFirst targetFirst sourceSecond targetSecond lcBool lcAt rcPort.1 rcPort.2 rcAt).2 pieces)
        · exact site.fan_body_double_copied_same_slot_reflect sourceMatches targetMatches flow positive principal selection first second physical leftPosition rightPosition leftSlot rightSlot leftIncoming rightIncoming sourceFirst sourceSecond targetLeft targetRight targetLeftChildWord targetRightChildWord lpBool rpBool lpAt rpAt lcBool rcBool lcAt rcAt
end
end Lamping.AG

#print axioms Lamping.AG.PathSite.fan_body_lambda_same_slot_forward
#print axioms Lamping.AG.PathSite.fan_body_lambda_same_slot_reflect
