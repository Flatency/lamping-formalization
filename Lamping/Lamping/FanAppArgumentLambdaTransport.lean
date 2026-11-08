import Lamping.Lamping.FanAppCopiedArgumentCuts
import Lamping.Lamping.FanAppFunctionVariableTransport
import Lamping.Lambda.PrerequisiteEdgeOrder
import Lamping.Lamping.FanLambdaEndpointCases
namespace Lamping.Lambda.Labelled
private theorem argument_parent
    (occurrence : SourceSubterm [] .external current leaf env ctx sub)
    (incoming : ∃stamp,ctx=.appArg stamp) :
    ∃ parent appStamp fn arg,leaf=parent++[.arg] ∧current.subterm parent=some (.app appStamp fn arg) := by
  rcases occurrence.last_departure with ⟨_,external⟩|⟨parent,step,term,split,lookup,role⟩
  · rcases incoming with ⟨stamp,equal⟩;cases external.symm.trans equal
  · cases role with
    | fn => rcases incoming with ⟨stamp,equal⟩;cases equal
    | arg => exact ⟨parent,_,_,_,split,lookup⟩
    | body => rcases incoming with ⟨stamp,equal⟩;cases equal
private theorem no_function_argument_end {p q : Path} : p++[.fn]≠q++[.arg] := by
  intro same
  have ends := congrArg List.getLast? same
  simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or] at ends
  cases ends

/-- The incoming lambda is actually read, then the actual APP parent's
function edge is the next read, including the redex-parent case. -/
theorem PrerequisiteChain.argument_lambda_next_function_slot {n : Nat}
    (chain : PrerequisiteChain current start edges)
    (slot : edges[n]?=some leaf)
    (atLambda : current.subterm leaf=some (.lam childStamp childBody))
    (occurrence : SourceSubterm [] .external current leaf env ctx sub)
    (incoming : ∃stamp,ctx=.appArg stamp) :
    ∃ parent appStamp fn more,leaf=parent++[.arg] ∧
      current.subterm parent=some (.app appStamp fn (.lam childStamp childBody)) ∧
      PrerequisiteChain current parent more ∧
      edges[n+1]?=some (parent++[.fn]) ∧PrerequisitePrefix current leaf [leaf] parent := by
  obtain ⟨parent,appStamp,fn,arg,lexical,parentLookup⟩ := argument_parent occurrence incoming
  have argLookup : current.subterm leaf=some arg := by
    rw [lexical,LTerm.subterm_append,parentLookup];cases arg <;> rfl
  have argEq : arg=.lam childStamp childBody := Option.some.inj (argLookup.symm.trans atLambda)
  subst arg
  obtain ⟨before,after,middle,split,_segment,remainder,reads⟩ :=
    chain.split_at_member (List.mem_of_getElem? slot)
  have atSplit : edges[before.length]?=some leaf := by
    rw [split,List.getElem?_append_right (Nat.le_refl _)];simp
  obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp slot
  have ordinal : n=before.length := List.getElem?_inj bound chain.nodup (slot.trans atSplit.symm)
  rcases reads with ⟨_,_,_,_,edgeEq⟩|⟨_,_,_,edgeEq⟩
  · exact False.elim (no_function_argument_end (edgeEq.symm.trans lexical))
  · rw [←edgeEq] at remainder
    rcases remainder.lambda_cases atLambda with ⟨otherParent,_,_,atFunction,_,_⟩|
      ⟨otherParent,step,tail,atParent,_notFunction,listEq,parentChain⟩
    · exact False.elim (no_function_argument_end (atFunction.symm.trans lexical))
    · have steps : step=.arg := by
        have ends := congrArg List.getLast? (atParent.symm.trans lexical)
        simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or] at ends
        exact Option.some.inj ends
      subst step
      have parents : otherParent=parent := List.append_cancel_right (atParent.symm.trans lexical)
      have tailEq : after=tail := (List.cons.inj listEq).2
      rw [parents,←tailEq] at parentChain
      have head : after.head?=some (parent++[.fn]) := by
        rcases parentChain.app_cases parentLookup with ⟨_,_,_,equal⟩|⟨_,_,equal,_⟩ <;> rw [equal] <;> rfl
      have segment : PrerequisitePrefix current leaf [leaf] parent := by
        rw [lexical] at atLambda ⊢
        exact .lam atLambda (by decide) .refl
      refine ⟨parent,appStamp,fn,after,lexical,parentLookup,parentChain,?_,segment⟩
      rw [ordinal,split,List.getElem?_append_right (by omega)]
      simpa only [Nat.add_sub_cancel_left,List.getElem?_cons_succ,←List.head?_eq_getElem?] using head

end Lamping.Lambda.Labelled
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.app i j lt) V) site.closed
private abbrev fanAppTransportRight (i j : Nat) (lt : i<j) := (Schema.fanAction Op.app i j lt).right.net
local notation "rhs" => fanAppTransportRight i j lt

theorem SourceEdgeFragment.fan_app_copied_argument_kept_forward
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceFirst : SourceEdgeFragment current site.net root leftEdge p)
    (targetFirst : SourceEdgeFragment current site.reduce root leftEdge p)
    (sourceSecond : SourceEdgeFragment current site.net root rightEdge q)
    (targetSecond : SourceEdgeFragment current site.reduce root rightEdge q)
    (leftRole : SourceDeparture leftTerm .arg leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm .arg rightEdge.fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[.arg])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[.arg])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[.arg])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[.arg])
    (branch : Bool)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),appCtx⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),appCtx⟩)))
    (leftTerminal rightTerminal : NodePort signature K kept)
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftTerminal.1,leftTerminal.2⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightTerminal.1,rightTerminal.2⟩)))
    (pieces : sourceFirst.segments=sourceSecond.segments) : targetFirst.segments=targetSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨leftRaw,leftOld,ls,leftShape,leftSource,leftRelation,leftPieceLabels⟩ :=
    sourceFirst.fan_app_copied_argument_kept_cut site flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord branch leftParentAt
      leftTerminal.1 leftTerminal.2 leftEndAt leftLabels
  obtain ⟨rightRaw,rightOld,rs,rightShape,rightSource,rightRelation,rightPieceLabels⟩ :=
    sourceSecond.fan_app_copied_argument_kept_cut site flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord branch rightParentAt
      rightTerminal.1 rightTerminal.2 rightEndAt rightLabels
  have sameOld : site.outsideEnd (.inr (.inl (.inr (.inr true))))::leftOld=
      site.outsideEnd (.inr (.inl (.inr (.inr true))))::rightOld :=
    leftSource.symm.trans (pieces.trans rightSource)
  have contiguous : sourceFirst.segments=[]++
      (site.outsideEnd (.inr (.inl (.inr (.inr true))))::leftOld)++[] := by
    simpa only [List.nil_append,List.append_nil] using leftSource
  have rawSame := sourceFirst.fan_target_unique_of_contiguous_source site leftRelation rightRelation
    leftPieceLabels rightPieceLabels sameOld contiguous
  have tails := (List.cons.inj rawSame).2
  have maps : targetFirst.segments.map (plugEnd (cut).label (rhs).label).invFun=
      targetSecond.segments.map (plugEnd (cut).label (rhs).label).invFun := by
    rw [leftShape,rightShape,tails]
  have physical := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label)) maps
  simpa only [plug_decomposition_flatten] using physical

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


private theorem copied_piece_forward
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceFirst : OccurrenceFragment current site.net root p)
    (targetFirst : OccurrenceFragment current site.reduce root p)
    (sourceSecond : OccurrenceFragment current site.net root q)
    (targetSecond : OccurrenceFragment current site.reduce root q)
    (leftRole : SourceDeparture leftTerm .arg (sourceEdge sourceFirst.environment sourceFirst.context sourceFirst.term).fromPort)
    (rightRole : SourceDeparture rightTerm .arg (sourceEdge sourceSecond.environment sourceSecond.context sourceSecond.term).fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[.arg])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[.arg])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[.arg])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[.arg])
    (branch : Bool)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),appCtx⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),appCtx⟩)))
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
  exact lsource.fan_app_copied_argument_kept_forward site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget leftRole rightRole sourceLeft sourceRight targetLeft targetRight
    sourceLeftWord sourceRightWord targetLeftWord targetRightWord branch leftParentAt rightParentAt
    leftTerminal rightTerminal leftEndAt rightEndAt pieces

private theorem parent_mixed_source_ne
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (matching : Matches site.net root current.erase) (principal : SiteActionPrincipal site)
    (sourceFirst : OccurrenceFragment current site.net root p)
    (sourceSecond : OccurrenceFragment current site.net root q)
    (leftRole : SourceDeparture leftTerm .arg (sourceEdge sourceFirst.environment sourceFirst.context sourceFirst.term).fromPort)
    (rightRole : SourceDeparture rightTerm .arg (sourceEdge sourceSecond.environment sourceSecond.context sourceSecond.term).fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[.arg])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[.arg])
    (leftWord : accessWord site.net sourceLeft.val=accessWord site.reduce targetLeft.val)
    (rightWord : accessWord site.net sourceRight.val=accessWord site.reduce targetRight.val)
    (branch : Bool)
    (leftAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),appCtx⟩)))
    (keptPort : NodePort signature K kept)
    (rightAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inl keptPort.1,keptPort.2⟩))) :
    sourceFirst.fragment.segments≠sourceSecond.fragment.segments := by
  obtain ⟨a,b,labels⟩ := targetLeft.property.1.1
  obtain ⟨_pending,_relation,_oldLabels,leftFinish,_shape⟩ :=
    site.fan_aux_canonical_access flow root positive matching principal sourceLeft targetLeft leftWord branch false leftAt labels
  obtain ⟨c,d,otherLabels⟩ := targetRight.property.1.1
  obtain ⟨_otherRelation,_oldOtherLabels,rightFinish⟩ :=
    site.action_kept_canonical_access (.fan .app i j lt) flow root positive matching principal
      sourceRight targetRight rightWord keptPort.1 keptPort.2 rightAt otherLabels
  obtain ⟨leftDep,leftHead⟩ := sourceFirst.fragment.head_node_of_parent matching leftRole sourceLeft sourceLeftWord
    (.inr (.inr ())) appCtx leftFinish
  obtain ⟨rightDep,rightHead⟩ := sourceSecond.fragment.head_node_of_parent matching rightRole sourceRight sourceRightWord
    (.inl keptPort.1) keptPort.2 rightFinish
  intro equal
  have heads := congrArg List.head? equal
  rw [leftHead,rightHead] at heads
  have nodes := congrArg Sigma.fst (Sum.inl.inj (Option.some.inj heads))
  cases nodes


private theorem selected_argument_role
    {current : LTerm} {root : B} (selection : OccurrenceFragmentSelection current site.net root)
    (lookup : current.subterm parent=some (.app stamp fn arg)) (position : Position current.erase)
    (atPosition : position.val=parent++[.arg]) :
    SourceDeparture (.app stamp fn arg) .arg
      (sourceEdge (selection position).environment (selection position).context (selection position).term).fromPort := by
  obtain ⟨env,ctx,outer⟩ := SourceSubterm.of_lookup current lookup [] .external
  have actual : SourceSubterm [] .external current position.val env (.appArg stamp) arg := by
    rw [atPosition];exact outer.append (.arg .nil)
  have context := ((selection position).occurrence.same_occurrence actual).2.1
  have sourceFrom : (sourceEdge (selection position).environment (selection position).context (selection position).term).fromPort=.appArg stamp := by
    cases (selection position).term <;> exact context
  rw [sourceFrom];exact .arg

theorem PathSite.fan_app_argument_lambda_same_slot_forward
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (inputs : RootInputs site.net root) (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site) (selection : OccurrenceFragmentSelection current site.net root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (leftLookup : current.subterm leftPosition.val=some (.lam leftStamp leftBody))
    (rightLookup : current.subterm rightPosition.val=some (.lam rightStamp rightBody))
    (leftIncoming : ∃stamp,(selection leftPosition).context=.appArg stamp)
    (rightIncoming : ∃stamp,(selection rightPosition).context=.appArg stamp)
    (targetFirst : OccurrenceFragment current site.reduce root leftPosition.val)
    (targetSecond : OccurrenceFragment current site.reduce root rightPosition.val) :
    targetFirst.fragment.segments=targetSecond.fragment.segments := by
  have pieces := same_chain_representation_slot selection first second physical leftPosition rightPosition leftSlot rightSlot
  let sourceFirst := selection leftPosition
  let sourceSecond := selection rightPosition
  obtain ⟨lp,la,lfn,le,lSplit,lLookup,_lChain,lNext,_lPrefix⟩ :=
    first.argument_lambda_next_function_slot leftSlot leftLookup sourceFirst.occurrence leftIncoming
  obtain ⟨rp,ra,rfn,re,rSplit,rLookup,_rChain,rNext,_rPrefix⟩ :=
    second.argument_lambda_next_function_slot rightSlot rightLookup sourceSecond.occurrence rightIncoming
  have lRole := selected_argument_role site selection lLookup leftPosition lSplit
  have rRole := selected_argument_role site selection rLookup rightPosition rSplit
  let leftParentPosition : Position current.erase := ⟨lp,by rw [←LTerm.erase_subterm,lLookup];rfl⟩
  let rightParentPosition : Position current.erase := ⟨rp,by rw [←LTerm.erase_subterm,rLookup];rfl⟩
  obtain ⟨sourceLeft,sourceLeftWord,_⟩ := Matches.observation site.net sourceMatches leftParentPosition
  obtain ⟨sourceRight,sourceRightWord,_⟩ := Matches.observation site.net sourceMatches rightParentPosition
  obtain ⟨targetLeft,targetLeftWord,_⟩ := Matches.observation site.reduce targetMatches leftParentPosition
  obtain ⟨targetRight,targetRightWord,_⟩ := Matches.observation site.reduce targetMatches rightParentPosition
  have excluded : ∀port : Port (.op .app),portKind (.op .app) port≠some AccessKind.lam := by
    intro port wrong
    rcases port with u|aux
    · cases u;cases wrong
    · cases aux <;> cases wrong
  have leftChildKind := targetMatches.lambda_access_typed leftLookup targetFirst.fragment.access targetFirst.fragment.word
  have rightChildKind := targetMatches.lambda_access_typed rightLookup targetSecond.fragment.access targetSecond.fragment.word
  obtain ⟨lcPort,lcAt⟩ := site.action_access_kept_of_kind_excluded (.fan .app i j lt) targetFirst.fragment.access leftChildKind excluded
  obtain ⟨rcPort,rcAt⟩ := site.action_access_kept_of_kind_excluded (.fan .app i j lt) targetSecond.fragment.access rightChildKind excluded
  have slWord : leftPosition.val=accessWord site.net sourceLeft.val++[.arg] := by rw [sourceLeftWord];exact lSplit
  have srWord : rightPosition.val=accessWord site.net sourceRight.val++[.arg] := by rw [sourceRightWord];exact rSplit
  have tlWord : leftPosition.val=accessWord site.reduce targetLeft.val++[.arg] := by rw [targetLeftWord];exact lSplit
  have trWord : rightPosition.val=accessWord site.reduce targetRight.val++[.arg] := by rw [targetRightWord];exact rSplit
  have lWord : accessWord site.net sourceLeft.val=accessWord site.reduce targetLeft.val := sourceLeftWord.trans targetLeftWord.symm
  have rWord : accessWord site.net sourceRight.val=accessWord site.reduce targetRight.val := sourceRightWord.trans targetRightWord.symm
  rcases site.fan_app_access_cases targetLeft with ⟨lpPort,lpAt⟩|⟨lb,lpAt⟩
  · rcases site.fan_app_access_cases targetRight with ⟨rpPort,rpAt⟩|⟨rb,rpAt⟩
    · exact (kept_piece_equality site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond lRole rRole sourceLeft sourceRight targetLeft targetRight slWord srWord tlWord trWord lpPort rpPort lcPort rcPort lpAt rpAt lcAt rcAt).mpr pieces
    · exact False.elim (parent_mixed_source_ne site flow root positive sourceMatches principal sourceSecond sourceFirst rRole lRole sourceRight sourceLeft targetRight targetLeft srWord slWord rWord lWord rb rpAt lpPort lpAt pieces.symm)
  · rcases site.fan_app_access_cases targetRight with ⟨rpPort,rpAt⟩|⟨rb,rpAt⟩
    · exact False.elim (parent_mixed_source_ne site flow root positive sourceMatches principal sourceFirst sourceSecond lRole rRole sourceLeft sourceRight targetLeft targetRight slWord srWord lWord rWord lb lpAt rpPort rpAt pieces)
    · have leftFnLookup : current.subterm (lp++[.fn])=some lfn := by
        rw [LTerm.subterm_append,lLookup];cases lfn <;> rfl
      have rightFnLookup : current.subterm (rp++[.fn])=some rfn := by
        rw [LTerm.subterm_append,rLookup];cases rfn <;> rfl
      let leftFnPosition : Position current.erase := ⟨lp++[.fn],by rw [←LTerm.erase_subterm,leftFnLookup];cases lfn <;> rfl⟩
      let rightFnPosition : Position current.erase := ⟨rp++[.fn],by rw [←LTerm.erase_subterm,rightFnLookup];cases rfn <;> rfl⟩
      have fnPieces := same_chain_representation_slot selection first second physical leftFnPosition rightFnPosition lNext rNext
      have leftFnRole := selected_function_role selection lLookup leftFnPosition rfl
      have rightFnRole := selected_function_role selection rLookup rightFnPosition rfl
      have leftFnWord : leftFnPosition.val=accessWord site.net sourceLeft.val++[.fn] := by rw [sourceLeftWord]
      have rightFnWord : rightFnPosition.val=accessWord site.net sourceRight.val++[.fn] := by rw [sourceRightWord]
      have leftReader := (selection leftFnPosition).fragment.fan_target_app_function_branch site sourceMatches inputs flow positive
        leftFnRole sourceLeft leftFnWord targetLeft lWord lb lpAt
      have rightReader := (selection rightFnPosition).fragment.fan_target_app_function_branch site sourceMatches inputs flow positive
        rightFnRole sourceRight rightFnWord targetRight rWord rb rpAt
      have sameBranch : lb=rb := (selection leftFnPosition).fragment.function_control_branch_unique site (Or.inl rfl) leftReader
        (by intro a b labels;exact rightReader a b (fnPieces ▸ labels))
      subst rb
      exact copied_piece_forward site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond
        lRole rRole sourceLeft sourceRight targetLeft targetRight slWord srWord tlWord trWord lb lpAt rpAt lcPort rcPort lcAt rcAt pieces
end
end Lamping.AG
#print axioms Lamping.Lambda.Labelled.PrerequisiteChain.argument_lambda_next_function_slot
#print axioms Lamping.AG.SourceEdgeFragment.fan_app_copied_argument_kept_forward
#print axioms Lamping.AG.PathSite.fan_app_argument_lambda_same_slot_forward
