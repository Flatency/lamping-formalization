import Lamping.Lamping.FanAppCopiedContextCuts
import Lamping.Lamping.FanAppReadSlotDispatcher
import Lamping.Lamping.FanAppArgumentLambdaTransport
import Lamping.Lamping.FanReadSlotDispatcher
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}
private theorem function_parent (occ : OccurrenceFragment current g root leaf)
    (incoming : ∃stamp,occ.context=.appFn stamp) :
    ∃parent stamp fn arg,current.subterm parent=some (.app stamp fn arg) ∧leaf=parent++[.fn] ∧
      SourceDeparture (.app stamp fn arg) .fn (sourceEdge occ.environment occ.context occ.term).fromPort := by
  rcases occ with ⟨sub,env,ctx,actual,frag⟩
  rcases actual.last_departure with ⟨_,external⟩|⟨parent,step,term,split,lookup,role⟩
  · obtain ⟨stamp,equal⟩:=incoming;cases external.symm.trans equal
  · cases role with
    | fn => cases sub <;> exact ⟨parent,_,_,_,lookup,split,.fn⟩
    | arg => obtain ⟨stamp,equal⟩:=incoming;cases equal
    | body => obtain ⟨stamp,equal⟩:=incoming;cases equal

private theorem argument_parent (occ : OccurrenceFragment current g root leaf)
    (incoming : ∃stamp,occ.context=.appArg stamp) :
    ∃parent stamp fn arg,current.subterm parent=some (.app stamp fn arg) ∧leaf=parent++[.arg] ∧
      SourceDeparture (.app stamp fn arg) .arg (sourceEdge occ.environment occ.context occ.term).fromPort := by
  rcases occ with ⟨sub,env,ctx,actual,frag⟩
  rcases actual.last_departure with ⟨_,external⟩|⟨parent,step,term,split,lookup,role⟩
  · obtain ⟨stamp,equal⟩:=incoming;cases external.symm.trans equal
  · cases role with
    | fn => obtain ⟨stamp,equal⟩:=incoming;cases equal
    | arg => cases sub <;> exact ⟨parent,_,_,_,lookup,split,.arg⟩
    | body => obtain ⟨stamp,equal⟩:=incoming;cases equal

private theorem function_argument_ne (matching : Matches g root current.erase)
    (first : OccurrenceFragment current g root p) (second : OccurrenceFragment current g root q)
    (leftIncoming : ∃stamp,first.context=.appFn stamp)
    (rightIncoming : ∃stamp,second.context=.appArg stamp) :
    first.fragment.segments≠second.fragment.segments := by
  obtain ⟨lp,la,lfn,larg,lLookup,lSplit,lRole⟩:=function_parent first leftIncoming
  obtain ⟨rp,ra,rfn,rarg,rLookup,rSplit,rRole⟩:=argument_parent second rightIncoming
  let lpos : Position current.erase:=⟨lp,by rw [←LTerm.erase_subterm,lLookup];rfl⟩
  let rpos : Position current.erase:=⟨rp,by rw [←LTerm.erase_subterm,rLookup];rfl⟩
  obtain ⟨lParent,lWord,_⟩:=Matches.observation g matching lpos
  obtain ⟨rParent,rWord,_⟩:=Matches.observation g matching rpos
  exact first.fragment.ne_of_child_steps matching second.fragment lRole rRole lParent rParent
    (by rw [lWord];exact lSplit) (by rw [rWord];exact rSplit) (by decide)

private theorem app_lambda_ne (matching : Matches g root current.erase)
    (first : OccurrenceFragment current g root p) (second : OccurrenceFragment current g root q)
    (leftLookup : current.subterm p=some (.app stamp fn arg))
    (rightLookup : current.subterm q=some (.lam origin body)) :
    first.fragment.segments≠second.fragment.segments := by
  intro pieces
  have kinds:=first.fragment.access_kind_eq_of_segments_eq second.fragment pieces
  rw [matching.app_access_typed leftLookup first.fragment.access first.fragment.word,
    matching.lambda_access_typed rightLookup second.fragment.access second.fragment.word] at kinds
  cases kinds
private theorem position_cases (position : Position current.erase) :
    ((∃stamp fn arg,current.subterm position.val=some (.app stamp fn arg)) ∨
      (∃stamp body,current.subterm position.val=some (.lam stamp body))) ∨
      (∃stamp index,current.subterm position.val=some (.var stamp index)) := by
  have valid := position.property
  cases lookup : current.subterm position.val with
  | none => rw [←LTerm.erase_subterm,lookup] at valid;cases valid
  | some term =>
    cases term with
    | app stamp fn arg => exact Or.inl (Or.inl ⟨stamp,fn,arg,rfl⟩)
    | lam stamp body => exact Or.inl (Or.inr ⟨stamp,body,rfl⟩)
    | var stamp index => exact Or.inr ⟨stamp,index,rfl⟩

private theorem proper_variable_ne (matching : Matches g root current.erase)
    (first : OccurrenceFragment current g root p) (second : OccurrenceFragment current g root q)
    (proper : (∃stamp fn arg,current.subterm p=some (.app stamp fn arg)) ∨
      (∃stamp body,current.subterm p=some (.lam stamp body)))
    (lookup : current.subterm q=some (.var stamp index)) :
    first.fragment.segments≠second.fragment.segments := by
  intro pieces
  have kinds := first.fragment.access_kind_eq_of_segments_eq second.fragment pieces
  rcases proper with ⟨a,fn,arg,actual⟩|⟨a,body,actual⟩
  · rw [matching.app_access_typed actual first.fragment.access first.fragment.word,
      matching.variable_access_typed lookup second.fragment.access second.fragment.word] at kinds
    cases kinds
  · rw [matching.lambda_access_typed actual first.fragment.access first.fragment.word,
      matching.variable_access_typed lookup second.fragment.access second.fragment.word] at kinds
    cases kinds
private theorem body_app_ne (matching : Matches g root current.erase)
    (first : OccurrenceFragment current g root p) (second : OccurrenceFragment current g root q)
    (leftIncoming : ∃stamp,first.context=.lamBody stamp)
    (rightIncoming : ∃stamp,second.context=.appFn stamp ∨second.context=.appArg stamp) :
    first.fragment.segments≠second.fragment.segments := by
  obtain ⟨lp,lo,lb,lLookup,lSplit,lRole⟩ := first.lambda_body_parent leftIncoming
  obtain ⟨rp,rstep,ra,rfn,rarg,rLookup,rSplit,rsteps,rRole⟩ := second.app_incoming_parent rightIncoming
  let leftParentPosition : Position current.erase := ⟨lp,by rw [←LTerm.erase_subterm,lLookup];rfl⟩
  let rightParentPosition : Position current.erase := ⟨rp,by rw [←LTerm.erase_subterm,rLookup];rfl⟩
  obtain ⟨leftParent,leftWord,_⟩ := Matches.observation g matching leftParentPosition
  obtain ⟨rightParent,rightWord,_⟩ := Matches.observation g matching rightParentPosition
  exact first.fragment.ne_of_child_steps matching second.fragment lRole rRole leftParent rightParent
    (by rw [leftWord];exact lSplit) (by rw [rightWord];exact rSplit)
    (by rcases rsteps with rfl|rfl <;> decide)
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
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

private theorem kept_copied_piece_forward
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
    (leftParent rightParent : NodePort signature K kept)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftParent.1,leftParent.2⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightParent.1,rightParent.2⟩)))
    (branch : Bool)
    (leftEndAt : targetFirst.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),appCtx⟩)))
    (rightEndAt : targetSecond.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),appCtx⟩)))
    (pieces : sourceFirst.fragment.segments=sourceSecond.fragment.segments) : targetFirst.fragment.segments=targetSecond.fragment.segments := by
  rcases sourceFirst with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetFirst with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceSecond with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetSecond with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact lsource.fan_kept_parent_copied_app_context_forward site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget leftRole rightRole sourceLeft sourceRight targetLeft targetRight
    sourceLeftWord sourceRightWord targetLeftWord targetRightWord leftParent rightParent leftParentAt rightParentAt
    branch leftEndAt rightEndAt pieces

private theorem double_copied_piece_forward
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
    (childBranch : Bool)
    (leftEndAt : targetFirst.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),appCtx⟩)))
    (rightEndAt : targetSecond.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),appCtx⟩)))
    (pieces : sourceFirst.fragment.segments=sourceSecond.fragment.segments) : targetFirst.fragment.segments=targetSecond.fragment.segments := by
  rcases sourceFirst with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetFirst with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceSecond with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetSecond with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact lsource.fan_copied_function_copied_app_context_forward site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget leftRole rightRole sourceLeft sourceRight targetLeft targetRight
    sourceLeftWord sourceRightWord targetLeftWord targetRightWord branch childBranch leftParentAt rightParentAt
    leftEndAt rightEndAt pieces

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

private theorem terminal_mixed_source_ne
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (matching : Matches site.net root current.erase) (principal : SiteActionPrincipal site)
    (sourceFirst : OccurrenceFragment current site.net root p)
    (targetFirst : OccurrenceFragment current site.reduce root p)
    (sourceSecond : OccurrenceFragment current site.net root q)
    (targetSecond : OccurrenceFragment current site.reduce root q)
    (branch : Bool)
    (copyAt : targetFirst.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),appCtx⟩)))
    (keptPort : NodePort signature K kept)
    (keptAt : targetSecond.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl keptPort.1,keptPort.2⟩))) :
    sourceFirst.fragment.segments≠sourceSecond.fragment.segments := by
  obtain ⟨a,b,labels⟩ := targetFirst.fragment.access.property.1.1
  obtain ⟨_,_,_,leftFinish,_⟩ := site.fan_aux_canonical_access flow root positive matching principal
    sourceFirst.fragment.access targetFirst.fragment.access (sourceFirst.fragment.word.trans targetFirst.fragment.word.symm)
    branch false copyAt labels
  obtain ⟨c,d,otherLabels⟩ := targetSecond.fragment.access.property.1.1
  obtain ⟨_,_,rightFinish⟩ := site.action_kept_canonical_access (.fan .app i j lt) flow root positive matching principal
    sourceSecond.fragment.access targetSecond.fragment.access (sourceSecond.fragment.word.trans targetSecond.fragment.word.symm)
    keptPort.1 keptPort.2 keptAt otherLabels
  exact sourceFirst.fragment.ne_of_terminal_nodes sourceSecond.fragment (.inr (.inr ())) (.inl keptPort.1)
    appCtx keptPort.2 leftFinish rightFinish (by intro wrong;cases wrong)

private theorem function_branches_equal
    {current : LTerm} {root : B} {boundary : B→Bool}
    (matching : Matches site.net root current.erase) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (sourceFirst : OccurrenceFragment current site.net root p)
    (sourceSecond : OccurrenceFragment current site.net root q)
    (leftRole : SourceDeparture leftTerm .fn (sourceEdge sourceFirst.environment sourceFirst.context sourceFirst.term).fromPort)
    (rightRole : SourceDeparture rightTerm .fn (sourceEdge sourceSecond.environment sourceSecond.context sourceSecond.term).fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[.fn])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[.fn])
    (leftWord : accessWord site.net sourceLeft.val=accessWord site.reduce targetLeft.val)
    (rightWord : accessWord site.net sourceRight.val=accessWord site.reduce targetRight.val)
    (lb rb : Bool)
    (leftAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl lb),appCtx⟩)))
    (rightAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rb),appCtx⟩)))
    (pieces : sourceFirst.fragment.segments=sourceSecond.fragment.segments) : lb=rb := by
  have leftReader:=sourceFirst.fragment.fan_target_app_function_branch site matching inputs flow positive
    leftRole sourceLeft sourceLeftWord targetLeft leftWord lb leftAt
  have rightReader:=sourceSecond.fragment.fan_target_app_function_branch site matching inputs flow positive
    rightRole sourceRight sourceRightWord targetRight rightWord rb rightAt
  exact sourceFirst.fragment.function_control_branch_unique site (Or.inl rfl) leftReader
    (by intro a b labels;exact rightReader a b (pieces ▸ labels))

private theorem copied_lookup_app
    {current : LTerm} {root : B} (matching : Matches site.reduce root current.erase)
    (position : Position current.erase) (fragment : OccurrenceFragment current site.reduce root position.val)
    (branch : Bool)
    (finish : fragment.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),appCtx⟩))) :
    ∃stamp fn arg,current.subterm position.val=some (.app stamp fn arg) := by
  have actual : accessKind site.reduce fragment.fragment.access.val=some .app := by
    simp only [accessKind,finish,Option.bind_some,Pairing.involutive];rfl
  cases lookup : current.subterm position.val with
  | none =>
    have valid:=position.property
    rw [←LTerm.erase_subterm,lookup] at valid
    cases valid
  | some term =>
    cases term with
    | app stamp fn arg => exact ⟨stamp,fn,arg,rfl⟩
    | lam stamp body =>
      have wrong:=matching.lambda_access_typed lookup fragment.fragment.access fragment.fragment.word
      cases actual.symm.trans wrong
    | var stamp index =>
      have wrong:=matching.variable_access_typed lookup fragment.fragment.access fragment.fragment.word
      cases actual.symm.trans wrong

/-- Child-copy Bool uses the APP's actual NEXT FUNCTION READ, not its
incoming APP piece equality and not the parent's current-slot Bool. -/
private theorem child_branches_equal
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (inputs : RootInputs site.net root) (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (selection : OccurrenceFragmentSelection current site.net root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (targetFirst : OccurrenceFragment current site.reduce root leftPosition.val)
    (targetSecond : OccurrenceFragment current site.reduce root rightPosition.val)
    (lb rb : Bool)
    (leftAt : targetFirst.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl lb),appCtx⟩)))
    (rightAt : targetSecond.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rb),appCtx⟩))) : lb=rb := by
  obtain ⟨la,lfn,larg,lLookup⟩:=copied_lookup_app site targetMatches leftPosition targetFirst lb leftAt
  obtain ⟨ra,rfn,rarg,rLookup⟩:=copied_lookup_app site targetMatches rightPosition targetSecond rb rightAt
  obtain ⟨_,_,lNext⟩:=first.app_read_next_function_slot leftSlot lLookup
  obtain ⟨_,_,rNext⟩:=second.app_read_next_function_slot rightSlot rLookup
  have lfLookup : current.subterm (leftPosition.val++[.fn])=some lfn := by
    rw [LTerm.subterm_append,lLookup];cases lfn <;> rfl
  have rfLookup : current.subterm (rightPosition.val++[.fn])=some rfn := by
    rw [LTerm.subterm_append,rLookup];cases rfn <;> rfl
  let lp : Position current.erase := ⟨leftPosition.val++[.fn],by rw [←LTerm.erase_subterm,lfLookup];cases lfn <;> rfl⟩
  let rp : Position current.erase := ⟨rightPosition.val++[.fn],by rw [←LTerm.erase_subterm,rfLookup];cases rfn <;> rfl⟩
  have pieces:=same_chain_representation_slot selection first second physical lp rp lNext rNext
  have lRole:=selected_function_role selection lLookup lp rfl
  have rRole:=selected_function_role selection rLookup rp rfl
  exact function_branches_equal site sourceMatches inputs flow positive (selection lp) (selection rp)
    lRole rRole (selection leftPosition).fragment.access (selection rightPosition).fragment.access
    targetFirst.fragment.access targetSecond.fragment.access
    (by rw [(selection leftPosition).fragment.word]) (by rw [(selection rightPosition).fragment.word])
    ((selection leftPosition).fragment.word.trans targetFirst.fragment.word.symm)
    ((selection rightPosition).fragment.word.trans targetSecond.fragment.word.symm) lb rb leftAt rightAt pieces

/-- Natural FUNCTION reading; both endpoint classifications and copy
synchronizations are internal. In particular terminal FN-lambda needs no NEXT. -/
private theorem function_same_slot_forward
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (inputs : RootInputs site.net root) (principal : SiteActionPrincipal site)
    (selection : OccurrenceFragmentSelection current site.net root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (leftIncoming : ∃stamp,(selection leftPosition).context=.appFn stamp)
    (rightIncoming : ∃stamp,(selection rightPosition).context=.appFn stamp)
    (targetFirst : OccurrenceFragment current site.reduce root leftPosition.val)
    (targetSecond : OccurrenceFragment current site.reduce root rightPosition.val) :
    targetFirst.fragment.segments=targetSecond.fragment.segments := by
  have pieces:=same_chain_representation_slot selection first second physical leftPosition rightPosition leftSlot rightSlot
  let sourceFirst:=selection leftPosition
  let sourceSecond:=selection rightPosition
  obtain ⟨lp,la,lfn,larg,lLookup,lSplit,lRole⟩:=function_parent sourceFirst leftIncoming
  obtain ⟨rp,ra,rfn,rarg,rLookup,rSplit,rRole⟩:=function_parent sourceSecond rightIncoming
  let lpos : Position current.erase:=⟨lp,by rw [←LTerm.erase_subterm,lLookup];rfl⟩
  let rpos : Position current.erase:=⟨rp,by rw [←LTerm.erase_subterm,rLookup];rfl⟩
  obtain ⟨sl,slw,_⟩:=Matches.observation site.net sourceMatches lpos
  obtain ⟨sr,srw,_⟩:=Matches.observation site.net sourceMatches rpos
  obtain ⟨tl,tlw,_⟩:=Matches.observation site.reduce targetMatches lpos
  obtain ⟨tr,trw,_⟩:=Matches.observation site.reduce targetMatches rpos
  have slWord : leftPosition.val=accessWord site.net sl.val++[.fn] := by rw [slw];exact lSplit
  have srWord : rightPosition.val=accessWord site.net sr.val++[.fn] := by rw [srw];exact rSplit
  have tlWord : leftPosition.val=accessWord site.reduce tl.val++[.fn] := by rw [tlw];exact lSplit
  have trWord : rightPosition.val=accessWord site.reduce tr.val++[.fn] := by rw [trw];exact rSplit
  have lw : accessWord site.net sl.val=accessWord site.reduce tl.val:=slw.trans tlw.symm
  have rw : accessWord site.net sr.val=accessWord site.reduce tr.val:=srw.trans trw.symm
  rcases site.fan_app_access_cases tl with ⟨lpp,lpAt⟩|⟨lpb,lpAt⟩
  · rcases site.fan_app_access_cases tr with ⟨rpp,rpAt⟩|⟨rpb,rpAt⟩
    · rcases site.fan_app_access_cases targetFirst.fragment.access with ⟨lcp,lcAt⟩|⟨lcb,lcAt⟩
      · rcases site.fan_app_access_cases targetSecond.fragment.access with ⟨rcp,rcAt⟩|⟨rcb,rcAt⟩
        · exact (kept_piece_equality site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond
            lRole rRole sl sr tl tr slWord srWord tlWord trWord lpp rpp lcp rcp lpAt rpAt lcAt rcAt).mpr pieces
        · exact False.elim (terminal_mixed_source_ne site flow root positive sourceMatches principal sourceSecond targetSecond sourceFirst targetFirst rcb rcAt lcp lcAt pieces.symm)
      · rcases site.fan_app_access_cases targetSecond.fragment.access with ⟨rcp,rcAt⟩|⟨rcb,rcAt⟩
        · exact False.elim (terminal_mixed_source_ne site flow root positive sourceMatches principal sourceFirst targetFirst sourceSecond targetSecond lcb lcAt rcp rcAt pieces)
        · have sameChild:=child_branches_equal site sourceMatches targetMatches inputs flow positive selection first second physical leftPosition rightPosition leftSlot rightSlot targetFirst targetSecond lcb rcb lcAt rcAt
          subst rcb
          exact kept_copied_piece_forward site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond
            lRole rRole sl sr tl tr slWord srWord tlWord trWord lpp rpp lpAt rpAt lcb lcAt rcAt pieces
    · exact False.elim (parent_mixed_source_ne site flow root positive sourceMatches principal sourceSecond sourceFirst rRole lRole sr sl tr tl srWord slWord rw lw rpb rpAt lpp lpAt pieces.symm)
  · rcases site.fan_app_access_cases tr with ⟨rpp,rpAt⟩|⟨rpb,rpAt⟩
    · exact False.elim (parent_mixed_source_ne site flow root positive sourceMatches principal sourceFirst sourceSecond lRole rRole sl sr tl tr slWord srWord lw rw lpb lpAt rpp rpAt pieces)
    · have sameParent:=function_branches_equal site sourceMatches inputs flow positive sourceFirst sourceSecond lRole rRole sl sr tl tr slWord srWord lw rw lpb rpb lpAt rpAt pieces
      subst rpb
      rcases site.fan_app_access_cases targetFirst.fragment.access with ⟨lcp,lcAt⟩|⟨lcb,lcAt⟩
      · rcases site.fan_app_access_cases targetSecond.fragment.access with ⟨rcp,rcAt⟩|⟨rcb,rcAt⟩
        · exact copied_piece_forward site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond
            lRole rRole sl sr tl tr slWord srWord tlWord trWord lpb lpAt rpAt lcp rcp lcAt rcAt pieces
        · exact False.elim (terminal_mixed_source_ne site flow root positive sourceMatches principal sourceSecond targetSecond sourceFirst targetFirst rcb rcAt lcp lcAt pieces.symm)
      · rcases site.fan_app_access_cases targetSecond.fragment.access with ⟨rcp,rcAt⟩|⟨rcb,rcAt⟩
        · exact False.elim (terminal_mixed_source_ne site flow root positive sourceMatches principal sourceFirst targetFirst sourceSecond targetSecond lcb lcAt rcp rcAt pieces)
        · have sameChild:=child_branches_equal site sourceMatches targetMatches inputs flow positive selection first second physical leftPosition rightPosition leftSlot rightSlot targetFirst targetSecond lcb rcb lcAt rcAt
          subst rcb
          exact double_copied_piece_forward site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond
            lRole rRole sl sr tl tr slWord srWord tlWord trWord lpb lpAt rpAt lcb lcAt rcAt pieces
private theorem body_lambda_same_slot_forward
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
  have excluded : ∀port : Port (.op .app),portKind (.op .app) port≠some AccessKind.lam := by
    intro port wrong
    rcases port with u|aux
    · cases u;cases wrong
    · cases aux <;> cases wrong
  obtain ⟨lpPort,lpAt⟩:=site.action_access_kept_of_kind_excluded (.fan .app i j lt) targetLeft leftParentKind excluded
  obtain ⟨rpPort,rpAt⟩:=site.action_access_kept_of_kind_excluded (.fan .app i j lt) targetRight rightParentKind excluded
  obtain ⟨lcPort,lcAt⟩:=site.action_access_kept_of_kind_excluded (.fan .app i j lt) targetFirst.fragment.access leftChildKind excluded
  obtain ⟨rcPort,rcAt⟩:=site.action_access_kept_of_kind_excluded (.fan .app i j lt) targetSecond.fragment.access rightChildKind excluded
  exact (kept_piece_equality site flow root positive sourceMatches targetMatches principal
    sourceFirst targetFirst sourceSecond targetSecond lRole rRole sourceLeft sourceRight targetLeft targetRight
    sourceLeftChildWord sourceRightChildWord targetLeftChildWord targetRightChildWord lpPort rpPort lcPort rcPort
    lpAt rpAt lcAt rcAt).mpr pieces

/-- Complete natural READ forward for the genuine fan-APP schema. Every
classification is derived from THIS actual lookup, role, and successful slot.
No parent/copy profile, endpoint, next ordinal, or piece equality is an input. -/
theorem PathSite.fan_app_all_read_same_slot_forward
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (inputs : RootInputs site.net root) (principal : SiteActionPrincipal site)
    (selection : OccurrenceFragmentSelection current site.net root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (targetFirst : OccurrenceFragment current site.reduce root leftPosition.val)
    (targetSecond : OccurrenceFragment current site.reduce root rightPosition.val) :
    targetFirst.fragment.segments=targetSecond.fragment.segments := by
  have pieces:=same_chain_representation_slot selection first second physical leftPosition rightPosition leftSlot rightSlot
  let sourceFirst:=selection leftPosition
  let sourceSecond:=selection rightPosition
  rcases position_cases leftPosition with leftProper|⟨la,li,leftLookup⟩
  · rcases position_cases rightPosition with rightProper|⟨ra,ri,rightLookup⟩
    · rcases leftProper with ⟨la,lfn,larg,leftLookup⟩|⟨la,lb,leftLookup⟩
      · rcases rightProper with ⟨ra,rfn,rarg,rightLookup⟩|⟨ra,rb,rightLookup⟩
        · exact function_same_slot_forward site sourceMatches targetMatches flow positive inputs principal selection
            first second physical leftPosition rightPosition leftSlot rightSlot
            (sourceFirst.app_read_incoming first (List.mem_of_getElem? leftSlot) leftLookup)
            (sourceSecond.app_read_incoming second (List.mem_of_getElem? rightSlot) rightLookup) targetFirst targetSecond
        · exact False.elim (app_lambda_ne sourceMatches sourceFirst sourceSecond leftLookup rightLookup pieces)
      · rcases rightProper with ⟨ra,rfn,rarg,rightLookup⟩|⟨ra,rb,rightLookup⟩
        · exact False.elim (app_lambda_ne sourceMatches sourceSecond sourceFirst rightLookup leftLookup pieces.symm)
        · rcases sourceFirst.read_incoming_cases first (List.mem_of_getElem? leftSlot) with lBody|⟨lo,lFnOrArg⟩
          · rcases sourceSecond.read_incoming_cases second (List.mem_of_getElem? rightSlot) with rBody|rApp
            · exact body_lambda_same_slot_forward site sourceMatches targetMatches flow positive principal selection
                first second physical leftPosition rightPosition leftSlot rightSlot leftLookup rightLookup lBody rBody targetFirst targetSecond
            · exact False.elim (body_app_ne sourceMatches sourceFirst sourceSecond lBody rApp pieces)
          · rcases sourceSecond.read_incoming_cases second (List.mem_of_getElem? rightSlot) with rBody|⟨ro,rFnOrArg⟩
            · exact False.elim (body_app_ne sourceMatches sourceSecond sourceFirst rBody ⟨lo,lFnOrArg⟩ pieces.symm)
            · rcases lFnOrArg with lFn|lArg
              · rcases rFnOrArg with rFn|rArg
                · exact function_same_slot_forward site sourceMatches targetMatches flow positive inputs principal selection
                    first second physical leftPosition rightPosition leftSlot rightSlot ⟨lo,lFn⟩ ⟨ro,rFn⟩ targetFirst targetSecond
                · exact False.elim (function_argument_ne sourceMatches sourceFirst sourceSecond ⟨lo,lFn⟩ ⟨ro,rArg⟩ pieces)
              · rcases rFnOrArg with rFn|rArg
                · exact False.elim (function_argument_ne sourceMatches sourceSecond sourceFirst ⟨ro,rFn⟩ ⟨lo,lArg⟩ pieces.symm)
                · exact site.fan_app_argument_lambda_same_slot_forward sourceMatches targetMatches inputs flow positive principal selection
                    first second physical leftPosition rightPosition leftSlot rightSlot leftLookup rightLookup
                    ⟨lo,lArg⟩ ⟨ro,rArg⟩ targetFirst targetSecond
    · exact False.elim (proper_variable_ne sourceMatches sourceFirst sourceSecond leftProper rightLookup pieces)
  · rcases position_cases rightPosition with rightProper|⟨ra,ri,rightLookup⟩
    · exact False.elim (proper_variable_ne sourceMatches sourceSecond sourceFirst rightProper leftLookup pieces.symm)
    · exact site.fan_app_function_variable_same_slot_forward sourceMatches targetMatches flow positive inputs principal selection
        first second physical leftPosition rightPosition leftSlot rightSlot leftLookup rightLookup targetFirst targetSecond
end
end Lamping.AG
#print axioms Lamping.AG.PathSite.fan_app_all_read_same_slot_forward
