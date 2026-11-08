import Lamping.Lamping.FanAppCopiedFunctionCuts
import Lamping.Lamping.FanKeptFragmentComparison
import Lamping.Lamping.FanProperOccurrenceCases
import Lamping.Lamping.FanVariableReadDispatcher
import Lamping.Lamping.ActionPrerequisiteCopyBranches
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.app i j lt) V) site.closed
private abbrev fanAppTransportRight (i j : Nat) (lt : i<j) := (Schema.fanAction Op.app i j lt).right.net
local notation "rhs" => fanAppTransportRight i j lt

theorem SourceEdgeFragment.fan_app_copied_function_kept_forward
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceFirst : SourceEdgeFragment current site.net root leftEdge p)
    (targetFirst : SourceEdgeFragment current site.reduce root leftEdge p)
    (sourceSecond : SourceEdgeFragment current site.net root rightEdge q)
    (targetSecond : SourceEdgeFragment current site.reduce root rightEdge q)
    (leftRole : SourceDeparture leftTerm .fn leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm .fn rightEdge.fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[.fn])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[.fn])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[.fn])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[.fn])
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
    sourceFirst.fan_app_copied_function_kept_cut site flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord branch leftParentAt
      leftTerminal.1 leftTerminal.2 leftEndAt leftLabels
  obtain ⟨rightRaw,rightOld,rs,rightShape,rightSource,rightRelation,rightPieceLabels⟩ :=
    sourceSecond.fan_app_copied_function_kept_cut site flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord branch rightParentAt
      rightTerminal.1 rightTerminal.2 rightEndAt rightLabels
  have sameOld : site.outsideEnd (.inr (.inl (.inr (.inl branch))))::leftOld=
      site.outsideEnd (.inr (.inl (.inr (.inl branch))))::rightOld := by
    have same := List.append_cancel_left (leftSource.symm.trans (pieces.trans rightSource))
    exact congrArg (fun xs=>site.outsideEnd (.inr (.inl (.inr (.inl branch))))::xs) (List.cons.inj same).2
  have contiguous : sourceFirst.segments=reverseEdges principal.edges++
      (site.outsideEnd (.inr (.inl (.inr (.inl branch))))::leftOld)++[] := by
    simpa only [List.append_nil] using leftSource
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
    (leftRole : SourceDeparture leftTerm .fn (sourceEdge sourceFirst.environment sourceFirst.context sourceFirst.term).fromPort)
    (rightRole : SourceDeparture rightTerm .fn (sourceEdge sourceSecond.environment sourceSecond.context sourceSecond.term).fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[.fn])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[.fn])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[.fn])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[.fn])
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
  exact lsource.fan_app_copied_function_kept_forward site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget leftRole rightRole sourceLeft sourceRight targetLeft targetRight
    sourceLeftWord sourceRightWord targetLeftWord targetRightWord branch leftParentAt rightParentAt
    leftTerminal rightTerminal leftEndAt rightEndAt pieces

private theorem parent_mixed_source_ne
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (matching : Matches site.net root current.erase) (principal : SiteActionPrincipal site)
    (sourceFirst : OccurrenceFragment current site.net root p)
    (sourceSecond : OccurrenceFragment current site.net root q)
    (leftRole : SourceDeparture leftTerm .fn (sourceEdge sourceFirst.environment sourceFirst.context sourceFirst.term).fromPort)
    (rightRole : SourceDeparture rightTerm .fn (sourceEdge sourceSecond.environment sourceSecond.context sourceSecond.term).fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[.fn])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[.fn])
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

theorem PathSite.fan_app_function_variable_same_slot_forward
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (inputs : RootInputs site.net root) (principal : SiteActionPrincipal site) (selection : OccurrenceFragmentSelection current site.net root)
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
  have excluded : ∀port : Port (.op .app),portKind (.op .app) port≠some AccessKind.var := by
    intro port wrong
    rcases port with u|aux
    · cases u;cases wrong
    · cases aux <;> cases wrong
  have leftChildKind := targetMatches.variable_access_typed leftLookup targetFirst.fragment.access targetFirst.fragment.word
  have rightChildKind := targetMatches.variable_access_typed rightLookup targetSecond.fragment.access targetSecond.fragment.word
  obtain ⟨lcPort,lcAt⟩ := site.action_access_kept_of_kind_excluded (.fan .app i j lt) targetFirst.fragment.access leftChildKind excluded
  obtain ⟨rcPort,rcAt⟩ := site.action_access_kept_of_kind_excluded (.fan .app i j lt) targetSecond.fragment.access rightChildKind excluded
  have slWord : leftPosition.val=accessWord site.net sourceLeft.val++[.fn] := by rw [sourceLeftWord];exact lSplit
  have srWord : rightPosition.val=accessWord site.net sourceRight.val++[.fn] := by rw [sourceRightWord];exact rSplit
  have tlWord : leftPosition.val=accessWord site.reduce targetLeft.val++[.fn] := by rw [targetLeftWord];exact lSplit
  have trWord : rightPosition.val=accessWord site.reduce targetRight.val++[.fn] := by rw [targetRightWord];exact rSplit
  have lWord : accessWord site.net sourceLeft.val=accessWord site.reduce targetLeft.val := sourceLeftWord.trans targetLeftWord.symm
  have rWord : accessWord site.net sourceRight.val=accessWord site.reduce targetRight.val := sourceRightWord.trans targetRightWord.symm
  rcases site.fan_app_access_cases targetLeft with ⟨lpPort,lpAt⟩|⟨lb,lpAt⟩
  · rcases site.fan_app_access_cases targetRight with ⟨rpPort,rpAt⟩|⟨rb,rpAt⟩
    · exact (kept_piece_equality site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond lRole rRole sourceLeft sourceRight targetLeft targetRight slWord srWord tlWord trWord lpPort rpPort lcPort rcPort lpAt rpAt lcAt rcAt).mpr pieces
    · exact False.elim (parent_mixed_source_ne site flow root positive sourceMatches principal sourceSecond sourceFirst rRole lRole sourceRight sourceLeft targetRight targetLeft srWord slWord rWord lWord rb rpAt lpPort lpAt pieces.symm)
  · rcases site.fan_app_access_cases targetRight with ⟨rpPort,rpAt⟩|⟨rb,rpAt⟩
    · exact False.elim (parent_mixed_source_ne site flow root positive sourceMatches principal sourceFirst sourceSecond lRole rRole sourceLeft sourceRight targetLeft targetRight slWord srWord lWord rWord lb lpAt rpPort rpAt pieces)
    · have leftReader := sourceFirst.fragment.fan_target_app_function_branch site sourceMatches inputs flow positive
        lRole sourceLeft slWord targetLeft lWord lb lpAt
      have rightReader := sourceSecond.fragment.fan_target_app_function_branch site sourceMatches inputs flow positive
        rRole sourceRight srWord targetRight rWord rb rpAt
      have sameBranch : lb=rb := sourceFirst.fragment.function_control_branch_unique site (Or.inl rfl) leftReader
        (by intro a b labels;exact rightReader a b (pieces ▸ labels))
      subst rb
      exact copied_piece_forward site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond
        lRole rRole sourceLeft sourceRight targetLeft targetRight slWord srWord tlWord trWord lb lpAt rpAt lcPort rcPort lcAt rcAt pieces
end
end Lamping.AG
#print axioms Lamping.AG.SourceEdgeFragment.fan_app_copied_function_kept_forward
#print axioms Lamping.AG.PathSite.fan_app_function_variable_same_slot_forward
