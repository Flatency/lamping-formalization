import Lamping.Lamping.FanAppChainRepresentationTransport
import Lamping.Lamping.FragmentTerminalSeparation
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
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.app i j lt) V) site.closed
private abbrev reflectionRight (i j : Nat) (lt : i<j) := (Schema.fanAction Op.app i j lt).right.net
local notation "rhs" => reflectionRight i j lt
private theorem plug_left_injective : Function.Injective (AG.plugLeft cut rhs) := by
  intro e f same
  have mapped := congrArg (plugEnd (cut).label (rhs).label).invFun same
  change (plugEnd (cut).label (rhs).label).invFun ((plugEnd (cut).label (rhs).label) (.inl e))=
    (plugEnd (cut).label (rhs).label).invFun ((plugEnd (cut).label (rhs).label) (.inl f)) at mapped
  rw [Bij.left_inv,Bij.left_inv] at mapped
  exact Sum.inl.inj mapped
private theorem SourceEdgeFragment.copied_function_kept_reflect
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
    (pieces : targetFirst.segments=targetSecond.segments) : sourceFirst.segments=sourceSecond.segments := by
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
  have maps := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label).invFun) pieces
  change targetFirst.segments.map (plugEnd (cut).label (rhs).label).invFun=_ at leftShape
  change targetSecond.segments.map (plugEnd (cut).label (rhs).label).invFun=_ at rightShape
  change targetFirst.segments.map (plugEnd (cut).label (rhs).label).invFun=
    targetSecond.segments.map (plugEnd (cut).label (rhs).label).invFun at maps
  rw [leftShape,rightShape] at maps
  have tails := (List.cons.inj (List.cons.inj maps).2).2
  have oldSame := leftRelation.fixed_source_unique_of_eq site rightRelation (by rw [tails])
  rw [leftSource,rightSource,(List.cons.inj oldSame).2]

private theorem SourceEdgeFragment.copied_argument_kept_reflect
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
    (pieces : targetFirst.segments=targetSecond.segments) : sourceFirst.segments=sourceSecond.segments := by
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
  have maps := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label).invFun) pieces
  change targetFirst.segments.map (plugEnd (cut).label (rhs).label).invFun=_ at leftShape
  change targetSecond.segments.map (plugEnd (cut).label (rhs).label).invFun=_ at rightShape
  change targetFirst.segments.map (plugEnd (cut).label (rhs).label).invFun=
    targetSecond.segments.map (plugEnd (cut).label (rhs).label).invFun at maps
  rw [leftShape,rightShape] at maps
  have tails := (List.cons.inj (List.cons.inj (List.cons.inj maps).2).2).2
  have oldSame := leftRelation.fixed_source_unique_of_eq site rightRelation (by rw [tails])
  rw [leftSource,rightSource,(List.cons.inj oldSame).2]

private theorem SourceEdgeFragment.kept_copied_context_reflect
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
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
    (childBranch : Bool)
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),appCtx⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),appCtx⟩)))
    (pieces : targetFirst.segments=targetSecond.segments) : sourceFirst.segments=sourceSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨lp,lr,ls,lo,leftOldLast,leftNewLast,leftShape,leftRelation,leftPieceLabels⟩ :=
    sourceFirst.fan_kept_parent_copied_app_context_cut site flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord leftParent.1 leftParent.2 leftParentAt childBranch leftEndAt leftLabels
  obtain ⟨rp,rr,rs,ro,rightOldLast,rightNewLast,rightShape,rightRelation,rightPieceLabels⟩ :=
    sourceSecond.fan_kept_parent_copied_app_context_cut site flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord rightParent.1 rightParent.2 rightParentAt childBranch rightEndAt rightLabels
  have maps := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label).invFun) pieces
  change targetFirst.segments.map (plugEnd (cut).label (rhs).label).invFun=_ at leftShape
  change targetSecond.segments.map (plugEnd (cut).label (rhs).label).invFun=_ at rightShape
  change targetFirst.segments.map (plugEnd (cut).label (rhs).label).invFun=
    targetSecond.segments.map (plugEnd (cut).label (rhs).label).invFun at maps
  rw [leftShape,rightShape] at maps
  have tails := List.append_cancel_right maps
  have parentSame := SourceEdgeFragment.equal_piece_parent_seams targetMatches targetFirst targetSecond
    leftRole rightRole targetLeft targetRight targetLeftWord targetRightWord pieces
  have pivotSame : lp=rp := plug_left_injective site
    (Option.some.inj (leftNewLast.symm.trans (parentSame.trans rightNewLast)))
  subst rp
  have oldSame := leftRelation.fixed_source_unique_of_eq site rightRelation (by rw [tails])
  exact (List.cons.inj oldSame).2

private theorem SourceEdgeFragment.double_copied_context_reflect
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
    (parentBranch childBranch : Bool)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl parentBranch),appCtx⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl parentBranch),appCtx⟩)))
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),appCtx⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl childBranch),appCtx⟩)))
    (pieces : targetFirst.segments=targetSecond.segments) : sourceFirst.segments=sourceSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨lp,lr,lo,ls,_leftSplit,leftShape,leftSource,leftRelation,leftPieceLabels⟩ :=
    sourceFirst.fan_copied_function_copied_app_context_cut site parentBranch childBranch flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord leftParentAt leftEndAt leftLabels
  obtain ⟨rp,rr,ro,rs,_rightSplit,rightShape,rightSource,rightRelation,rightPieceLabels⟩ :=
    sourceSecond.fan_copied_function_copied_app_context_cut site parentBranch childBranch flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord rightParentAt rightEndAt rightLabels
  have maps := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label).invFun) pieces
  change targetFirst.segments.map (plugEnd (cut).label (rhs).label).invFun=_ at leftShape
  change targetSecond.segments.map (plugEnd (cut).label (rhs).label).invFun=_ at rightShape
  change targetFirst.segments.map (plugEnd (cut).label (rhs).label).invFun=
    targetSecond.segments.map (plugEnd (cut).label (rhs).label).invFun at maps
  rw [leftShape,rightShape] at maps
  have tails := List.append_cancel_right (List.cons.inj (List.cons.inj maps).2).2
  change lr=rr at tails
  have oldSame := leftRelation.fixed_source_unique_of_eq site rightRelation (by rw [tails])
  rw [leftSource,rightSource,(List.cons.inj oldSame).2]

private theorem SourceEdgeFragment.function_piece_reflect
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
    (pieces : targetFirst.segments=targetSecond.segments) : sourceFirst.segments=sourceSecond.segments := by
  have parentSame := SourceEdgeFragment.equal_piece_parent_seams targetMatches targetFirst targetSecond
    leftRole rightRole targetLeft targetRight targetLeftWord targetRightWord pieces
  have terminalSame : targetFirst.access.val.getLast?=targetSecond.access.val.getLast? := by
    rw [←targetFirst.segments_last_eq_access_last,←targetSecond.segments_last_eq_access_last,pieces]
  rcases site.fan_app_access_cases targetLeft with ⟨lp,lpAt⟩|⟨pb,lpAt⟩
  · have rpAt := parentSame.symm.trans lpAt
    rcases site.fan_app_access_cases targetFirst.access with ⟨lc,lcAt⟩|⟨cb,lcAt⟩
    · have rcAt := terminalSame.symm.trans lcAt
      exact (sourceFirst.fan_kept_piece_equality site flow root positive sourceMatches targetMatches principal
        targetFirst sourceSecond targetSecond leftRole rightRole sourceLeft sourceRight targetLeft targetRight
        sourceLeftWord sourceRightWord targetLeftWord targetRightWord lp lp lc lc lpAt rpAt lcAt rcAt).mp pieces
    · have rcAt := terminalSame.symm.trans lcAt
      exact sourceFirst.kept_copied_context_reflect site flow root positive sourceMatches targetMatches principal
        targetFirst sourceSecond targetSecond leftRole rightRole sourceLeft sourceRight targetLeft targetRight
        sourceLeftWord sourceRightWord targetLeftWord targetRightWord lp lp lpAt rpAt cb lcAt rcAt pieces
  · have rpAt := parentSame.symm.trans lpAt
    rcases site.fan_app_access_cases targetFirst.access with ⟨lc,lcAt⟩|⟨cb,lcAt⟩
    · have rcAt := terminalSame.symm.trans lcAt
      exact sourceFirst.copied_function_kept_reflect site flow root positive sourceMatches targetMatches principal
        targetFirst sourceSecond targetSecond leftRole rightRole sourceLeft sourceRight targetLeft targetRight
        sourceLeftWord sourceRightWord targetLeftWord targetRightWord pb lpAt rpAt lc lc lcAt rcAt pieces
    · have rcAt := terminalSame.symm.trans lcAt
      exact sourceFirst.double_copied_context_reflect site flow root positive sourceMatches targetMatches principal
        targetFirst sourceSecond targetSecond leftRole rightRole sourceLeft sourceRight targetLeft targetRight
        sourceLeftWord sourceRightWord targetLeftWord targetRightWord pb cb lpAt rpAt lcAt rcAt pieces
private theorem function_occurrence_reflect
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {p q : Path}
    (sourceFirst : OccurrenceFragment current site.net root p)
    (targetFirst : OccurrenceFragment current site.reduce root p)
    (sourceSecond : OccurrenceFragment current site.net root q)
    (targetSecond : OccurrenceFragment current site.reduce root q)
    {leftTerm rightTerm : LTerm}
    (leftRole : SourceDeparture leftTerm .fn (sourceEdge sourceFirst.environment sourceFirst.context sourceFirst.term).fromPort)
    (rightRole : SourceDeparture rightTerm .fn (sourceEdge sourceSecond.environment sourceSecond.context sourceSecond.term).fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[.fn])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[.fn])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[.fn])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[.fn])
    (pieces : targetFirst.fragment.segments=targetSecond.fragment.segments) :
    sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  rcases sourceFirst with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetFirst with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceSecond with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetSecond with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact lsource.function_piece_reflect site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget leftRole rightRole sourceLeft sourceRight targetLeft targetRight
    sourceLeftWord sourceRightWord targetLeftWord targetRightWord pieces
private theorem kept_occurrence_reflect
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
    (rightEndAt : targetSecond.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightEnd.1,rightEnd.2⟩)))
    (pieces : targetFirst.fragment.segments=targetSecond.fragment.segments) :
    sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  rcases sourceFirst with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetFirst with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceSecond with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetSecond with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact (lsource.fan_kept_piece_equality site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget leftRole rightRole sourceLeft sourceRight targetLeft targetRight
    sourceLeftWord sourceRightWord targetLeftWord targetRightWord leftParent rightParent leftEnd rightEnd
    leftParentAt rightParentAt leftEndAt rightEndAt).mp pieces
private theorem function_same_slot_reflect
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site)
    {leftPosition rightPosition : Position current.erase}
    (sourceFirst : OccurrenceFragment current site.net root leftPosition.val)
    (sourceSecond : OccurrenceFragment current site.net root rightPosition.val)
    (leftIncoming : ∃stamp,sourceFirst.context=.appFn stamp)
    (rightIncoming : ∃stamp,sourceSecond.context=.appFn stamp)
    (targetFirst : OccurrenceFragment current site.reduce root leftPosition.val)
    (targetSecond : OccurrenceFragment current site.reduce root rightPosition.val)
    (pieces : targetFirst.fragment.segments=targetSecond.fragment.segments) :
    sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
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
  exact function_occurrence_reflect site flow root positive sourceMatches targetMatches principal
    sourceFirst targetFirst sourceSecond targetSecond lRole rRole sl sr tl tr
    slWord srWord tlWord trWord pieces
private theorem argument_occurrence_reflect
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
    (pieces : targetFirst.fragment.segments=targetSecond.fragment.segments) : sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  rcases sourceFirst with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetFirst with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceSecond with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetSecond with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact lsource.copied_argument_kept_reflect site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget leftRole rightRole sourceLeft sourceRight targetLeft targetRight
    sourceLeftWord sourceRightWord targetLeftWord targetRightWord branch leftParentAt rightParentAt
    leftTerminal rightTerminal leftEndAt rightEndAt pieces
private theorem argument_lambda_reflect
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site)
    {leftPosition rightPosition : Position current.erase}
    (sourceFirst : OccurrenceFragment current site.net root leftPosition.val)
    (sourceSecond : OccurrenceFragment current site.net root rightPosition.val)
    (leftLookup : current.subterm leftPosition.val=some (.lam leftStamp leftBody))
    (rightLookup : current.subterm rightPosition.val=some (.lam rightStamp rightBody))
    (leftIncoming : ∃stamp,sourceFirst.context=.appArg stamp)
    (rightIncoming : ∃stamp,sourceSecond.context=.appArg stamp)
    (targetFirst : OccurrenceFragment current site.reduce root leftPosition.val)
    (targetSecond : OccurrenceFragment current site.reduce root rightPosition.val)
    (pieces : targetFirst.fragment.segments=targetSecond.fragment.segments) :
    sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  obtain ⟨lp,la,lfn,larg,lLookup,lSplit,lRole⟩:=argument_parent sourceFirst leftIncoming
  obtain ⟨rp,ra,rfn,rarg,rLookup,rSplit,rRole⟩:=argument_parent sourceSecond rightIncoming
  let lpos : Position current.erase:=⟨lp,by rw [←LTerm.erase_subterm,lLookup];rfl⟩
  let rpos : Position current.erase:=⟨rp,by rw [←LTerm.erase_subterm,rLookup];rfl⟩
  obtain ⟨sl,slw,_⟩:=Matches.observation site.net sourceMatches lpos
  obtain ⟨sr,srw,_⟩:=Matches.observation site.net sourceMatches rpos
  obtain ⟨tl,tlw,_⟩:=Matches.observation site.reduce targetMatches lpos
  obtain ⟨tr,trw,_⟩:=Matches.observation site.reduce targetMatches rpos
  have slWord : leftPosition.val=accessWord site.net sl.val++[.arg] := by rw [slw];exact lSplit
  have srWord : rightPosition.val=accessWord site.net sr.val++[.arg] := by rw [srw];exact rSplit
  have tlWord : leftPosition.val=accessWord site.reduce tl.val++[.arg] := by rw [tlw];exact lSplit
  have trWord : rightPosition.val=accessWord site.reduce tr.val++[.arg] := by rw [trw];exact rSplit
  have lw : accessWord site.net sl.val=accessWord site.reduce tl.val:=slw.trans tlw.symm
  have rw : accessWord site.net sr.val=accessWord site.reduce tr.val:=srw.trans trw.symm
  have excluded : ∀port : Port (.op .app),portKind (.op .app) port≠some AccessKind.lam := by
    intro port wrong
    rcases port with u|aux
    · cases u;cases wrong
    · cases aux <;> cases wrong
  obtain ⟨lc,lcAt⟩:=site.action_access_kept_of_kind_excluded (.fan .app i j lt)
    targetFirst.fragment.access (targetMatches.lambda_access_typed leftLookup targetFirst.fragment.access targetFirst.fragment.word) excluded
  obtain ⟨rc,rcAt⟩:=site.action_access_kept_of_kind_excluded (.fan .app i j lt)
    targetSecond.fragment.access (targetMatches.lambda_access_typed rightLookup targetSecond.fragment.access targetSecond.fragment.word) excluded
  have parentSame := SourceEdgeFragment.equal_piece_parent_seams targetMatches targetFirst.fragment targetSecond.fragment
    (by simpa only [(sourceFirst.occurrence.same_occurrence targetFirst.occurrence).2.1,(sourceFirst.occurrence.same_occurrence targetFirst.occurrence).1,(sourceFirst.occurrence.same_occurrence targetFirst.occurrence).2.2] using lRole)
    (by simpa only [(sourceSecond.occurrence.same_occurrence targetSecond.occurrence).2.1,(sourceSecond.occurrence.same_occurrence targetSecond.occurrence).1,(sourceSecond.occurrence.same_occurrence targetSecond.occurrence).2.2] using rRole)
    tl tr tlWord trWord pieces
  rcases site.fan_app_access_cases tl with ⟨lp,lpAt⟩|⟨pb,lpAt⟩
  · have rpAt := parentSame.symm.trans lpAt
    exact kept_occurrence_reflect site flow root positive sourceMatches targetMatches principal
      sourceFirst targetFirst sourceSecond targetSecond lRole rRole sl sr tl tr
      slWord srWord tlWord trWord lp lp lc rc lpAt rpAt lcAt rcAt pieces
  · have rpAt := parentSame.symm.trans lpAt
    exact argument_occurrence_reflect site flow root positive sourceMatches targetMatches principal
      sourceFirst targetFirst sourceSecond targetSecond lRole rRole sl sr tl tr
      slWord srWord tlWord trWord pb lpAt rpAt lc rc lcAt rcAt pieces
private theorem body_lambda_reflect
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site)
    {leftPosition rightPosition : Position current.erase}
    (sourceFirst : OccurrenceFragment current site.net root leftPosition.val)
    (sourceSecond : OccurrenceFragment current site.net root rightPosition.val)
    (leftLookup : current.subterm leftPosition.val=some (.lam leftStamp leftBody))
    (rightLookup : current.subterm rightPosition.val=some (.lam rightStamp rightBody))
    (leftIncoming : ∃stamp,sourceFirst.context=.lamBody stamp)
    (rightIncoming : ∃stamp,sourceSecond.context=.lamBody stamp)
    (targetFirst : OccurrenceFragment current site.reduce root leftPosition.val)
    (targetSecond : OccurrenceFragment current site.reduce root rightPosition.val)
    (pieces : targetFirst.fragment.segments=targetSecond.fragment.segments) : sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
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
  exact (kept_occurrence_reflect site flow root positive sourceMatches targetMatches principal
    sourceFirst targetFirst sourceSecond targetSecond lRole rRole sourceLeft sourceRight targetLeft targetRight
    sourceLeftChildWord sourceRightChildWord targetLeftChildWord targetRightChildWord lpPort rpPort lcPort rcPort
    lpAt rpAt lcAt rcAt pieces)

private theorem variable_reflect
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (sourceFirst : OccurrenceFragment current site.net root leftPosition.val)
    (sourceSecond : OccurrenceFragment current site.net root rightPosition.val)
    (targetFirst : OccurrenceFragment current site.reduce root leftPosition.val)
    (targetSecond : OccurrenceFragment current site.reduce root rightPosition.val)
    (leftLookup : current.subterm leftPosition.val=some (.var leftStamp leftIndex))
    (rightLookup : current.subterm rightPosition.val=some (.var rightStamp rightIndex))
    (pieces : targetFirst.fragment.segments=targetSecond.fragment.segments) :
    sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  obtain ⟨_,_,_,_,_,lRole⟩:=sourceFirst.variable_function_parent first leftSlot leftLookup
  obtain ⟨_,_,_,_,_,rRole⟩:=sourceSecond.variable_function_parent second rightSlot rightLookup
  have lFrom : (sourceEdge sourceFirst.environment sourceFirst.context sourceFirst.term).fromPort=sourceFirst.context := by cases sourceFirst.term <;> rfl
  have rFrom : (sourceEdge sourceSecond.environment sourceSecond.context sourceSecond.term).fromPort=sourceSecond.context := by cases sourceSecond.term <;> rfl
  rw [lFrom] at lRole
  rw [rFrom] at rRole
  have li : ∃stamp,sourceFirst.context=.appFn stamp := by
    cases actual : sourceFirst.context <;> rw [actual] at lRole <;> cases lRole
    exact ⟨_,rfl⟩
  have ri : ∃stamp,sourceSecond.context=.appFn stamp := by
    cases actual : sourceSecond.context <;> rw [actual] at rRole <;> cases rRole
    exact ⟨_,rfl⟩
  exact function_same_slot_reflect site sourceMatches targetMatches flow positive principal
    sourceFirst sourceSecond li ri targetFirst targetSecond pieces

/-- Reflection compares only actual successful READ slots. TARGET literal
heads and lasts recover both finite copy profiles; no SOURCE equality or
branch profile is supplied, and no forward mixed contradiction is reversed. -/
theorem PathSite.fan_app_all_read_same_slot_reflect
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (_inputs : RootInputs site.net root) (principal : SiteActionPrincipal site)
    (selection : OccurrenceFragmentSelection current site.reduce root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (sourceFirst : OccurrenceFragment current site.net root leftPosition.val)
    (sourceSecond : OccurrenceFragment current site.net root rightPosition.val) :
    sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  have pieces:=same_chain_representation_slot selection first second physical leftPosition rightPosition leftSlot rightSlot
  let targetFirst:=selection leftPosition
  have lctx:= (sourceFirst.occurrence.same_occurrence targetFirst.occurrence).2.1
  let targetSecond:=selection rightPosition
  have rctx:= (sourceSecond.occurrence.same_occurrence targetSecond.occurrence).2.1
  rcases position_cases leftPosition with leftProper|⟨la,li,leftLookup⟩
  · rcases position_cases rightPosition with rightProper|⟨ra,ri,rightLookup⟩
    · rcases leftProper with ⟨la,lfn,larg,leftLookup⟩|⟨la,lb,leftLookup⟩
      · rcases rightProper with ⟨ra,rfn,rarg,rightLookup⟩|⟨ra,rb,rightLookup⟩
        · exact function_same_slot_reflect site sourceMatches targetMatches flow positive principal sourceFirst sourceSecond
            (sourceFirst.app_read_incoming first (List.mem_of_getElem? leftSlot) leftLookup)
            (sourceSecond.app_read_incoming second (List.mem_of_getElem? rightSlot) rightLookup) targetFirst targetSecond pieces
        · exact False.elim (app_lambda_ne targetMatches targetFirst targetSecond leftLookup rightLookup pieces)
      · rcases rightProper with ⟨ra,rfn,rarg,rightLookup⟩|⟨ra,rb,rightLookup⟩
        · exact False.elim (app_lambda_ne targetMatches targetSecond targetFirst rightLookup leftLookup pieces.symm)
        · rcases sourceFirst.read_incoming_cases first (List.mem_of_getElem? leftSlot) with lBody|⟨lo,lFnOrArg⟩
          · rcases sourceSecond.read_incoming_cases second (List.mem_of_getElem? rightSlot) with rBody|rApp
            · exact body_lambda_reflect site sourceMatches targetMatches flow positive principal sourceFirst sourceSecond leftLookup rightLookup lBody rBody targetFirst targetSecond pieces
            · exact False.elim (body_app_ne targetMatches targetFirst targetSecond (by simpa only [lctx] using lBody) (by simpa only [rctx] using rApp) pieces)
          · rcases sourceSecond.read_incoming_cases second (List.mem_of_getElem? rightSlot) with rBody|⟨ro,rFnOrArg⟩
            · exact False.elim (body_app_ne targetMatches targetSecond targetFirst (by simpa only [rctx] using rBody) (by simpa only [lctx] using (⟨lo,lFnOrArg⟩ : ∃stamp,sourceFirst.context=.appFn stamp ∨sourceFirst.context=.appArg stamp)) pieces.symm)
            · rcases lFnOrArg with lFn|lArg
              · rcases rFnOrArg with rFn|rArg
                · exact function_same_slot_reflect site sourceMatches targetMatches flow positive principal sourceFirst sourceSecond ⟨lo,lFn⟩ ⟨ro,rFn⟩ targetFirst targetSecond pieces
                · exact False.elim (function_argument_ne targetMatches targetFirst targetSecond (by simpa only [lctx] using (⟨lo,lFn⟩ : ∃stamp,sourceFirst.context=.appFn stamp)) (by simpa only [rctx] using (⟨ro,rArg⟩ : ∃stamp,sourceSecond.context=.appArg stamp)) pieces)
              · rcases rFnOrArg with rFn|rArg
                · exact False.elim (function_argument_ne targetMatches targetSecond targetFirst (by simpa only [rctx] using (⟨ro,rFn⟩ : ∃stamp,sourceSecond.context=.appFn stamp)) (by simpa only [lctx] using (⟨lo,lArg⟩ : ∃stamp,sourceFirst.context=.appArg stamp)) pieces.symm)
                · exact argument_lambda_reflect site sourceMatches targetMatches flow positive principal sourceFirst sourceSecond leftLookup rightLookup
                    ⟨lo,lArg⟩ ⟨ro,rArg⟩ targetFirst targetSecond pieces
    · exact False.elim (proper_variable_ne targetMatches targetFirst targetSecond leftProper rightLookup pieces)
  · rcases position_cases rightPosition with rightProper|⟨ra,ri,rightLookup⟩
    · exact False.elim (proper_variable_ne targetMatches targetSecond targetFirst rightProper leftLookup pieces.symm)
    · exact variable_reflect site sourceMatches targetMatches flow positive principal first second leftPosition rightPosition
        leftSlot rightSlot sourceFirst sourceSecond targetFirst targetSecond leftLookup rightLookup pieces
end
end Lamping.AG
#print axioms Lamping.AG.PathSite.fan_app_all_read_same_slot_reflect
