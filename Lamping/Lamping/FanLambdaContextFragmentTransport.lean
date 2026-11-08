import Lamping.Lamping.FanCopiedLambdaContextCuts
import Lamping.Lamping.ActualFragmentFanUniqueness
import Lamping.Lamping.FanLambdaSlotSynchronization
import Lamping.Lamping.ActionSyntaxObservationKinds
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.lam i j lt) V) site.closed
private abbrev fanContextTransportRight (i j : Nat) (lt : i<j) := (Schema.fanAction Op.lam i j lt).right.net
local notation "rhs" => fanContextTransportRight i j lt
/-- Two actual outside segments cannot begin a fan RHS through block. -/
private theorem local_nonempty {principal : SiteActionPrincipal site} {inside old}
    (route : ActionCanonicalLocal site principal inside old) : inside≠[] := by
  cases route with
  | fan actual => cases actual <;> simp [fanCrossEdges,fanPassiveEdges,reverseEdges]
private theorem peel_outside {principal : SiteActionPrincipal site} {pivot first : Endpoint cut}
    {raw whole tail old} (relation : ActionCanonicalBlocks site principal raw whole)
    (rawShape : raw=.inl pivot::.inl first::tail)
    (oldShape : whole=site.outsideEnd pivot::old) :
    ActionCanonicalBlocks site principal (.inl first::tail) old := by
  cases relation with
  | single e =>
    have lengths := congrArg List.length rawShape
    simp only [List.length_cons,List.length_nil] at lengths
    omega
  | outside rest =>
    have rawParts := List.cons.inj rawShape
    have firstEq := Sum.inl.inj rawParts.1
    subst pivot
    have oldParts := List.cons.inj oldShape
    rw [rawParts.2,oldParts.2] at rest
    exact rest
  | through inside front route start rest =>
    have rawAfter := (List.cons.inj rawShape).2
    have nonempty := local_nonempty site route
    cases inside with
    | nil => exact False.elim (nonempty rfl)
    | cons e es => cases (List.cons.inj rawAfter).1
private theorem trimmed_head {node : K} {departure : Port (kept node).sort}
    {physical : List (Endpoint site.reduce)} {raw : List (PlugSegment cut rhs)} {branch : Bool}
    (head : physical.head?=some (.inl ⟨.inl node,departure⟩))
    (shape : physical.map (plugEnd (cut).label (rhs).label).invFun=
      raw++[.inr (.inr (.inl (.inl branch)))]) :
    ∃first tail,raw=Sum.inl first::tail := by
  have mapped : (physical.map (plugEnd (cut).label (rhs).label).invFun).head?=
      some (.inl (.inl ⟨node,departure⟩)) := by
    rw [List.head?_map,head]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl (.inl ⟨node,departure⟩)))
  rw [shape] at mapped
  cases raw with
  | nil => cases Option.some.inj mapped
  | cons e tail =>
    have same : e=.inl (.inl ⟨node,departure⟩) := Option.some.inj mapped
    exact ⟨_,tail,by rw [same]⟩

/-- SAME copied context plus source-piece equality transports an actual
kept-parent fragment. The normalized source is contiguous in THIS fragment;
no padded NoPassive assertion or unary target-uniqueness is assumed. -/
theorem SourceEdgeFragment.fan_kept_parent_copied_context_forward
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {leftEdge rightEdge : SourceEdge} {p q : Path}
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
    (branch : Bool)
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)))
    (pieces : sourceFirst.segments=sourceSecond.segments) : targetFirst.segments=targetSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨lp,leftRaw,leftOld,ls,_leftOldLast,_leftNewLast,leftSource,leftShape,leftRelation,leftPieceLabels⟩ :=
    sourceFirst.fan_kept_parent_copied_context_cut site flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord leftParent.1 leftParent.2
      leftParentAt branch leftEndAt leftLabels
  obtain ⟨rp,rightRaw,rightOld,rs,_rightOldLast,_rightNewLast,rightSource,rightShape,rightRelation,rightPieceLabels⟩ :=
    sourceSecond.fan_kept_parent_copied_context_cut site flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord rightParent.1 rightParent.2
      rightParentAt branch rightEndAt rightLabels
  have oldSame : leftOld=rightOld := List.append_cancel_right (leftSource.symm.trans (pieces.trans rightSource))
  obtain ⟨ld,leftHead⟩ := targetFirst.head_node_of_parent targetMatches leftRole targetLeft targetLeftWord
    (.inl leftParent.1) leftParent.2 leftParentAt
  obtain ⟨rd,rightHead⟩ := targetSecond.head_node_of_parent targetMatches rightRole targetRight targetRightWord
    (.inl rightParent.1) rightParent.2 rightParentAt
  obtain ⟨lf,ltail,leftRawShape⟩ := trimmed_head site leftHead leftShape
  obtain ⟨rf,rtail,rightRawShape⟩ := trimmed_head site rightHead rightShape
  rw [leftRawShape] at leftRelation leftPieceLabels
  rw [rightRawShape] at rightRelation rightPieceLabels
  have leftCanonical := peel_outside site leftRelation rfl rfl
  have rightCanonical := peel_outside site rightRelation rfl rfl
  obtain ⟨_leftMiddle,_leftTurn,leftNormalizedLabels⟩ := leftPieceLabels.left_step
  obtain ⟨_rightMiddle,_rightTurn,rightNormalizedLabels⟩ := rightPieceLabels.left_step
  have rawSame := sourceFirst.fan_target_unique_of_contiguous_source site leftCanonical rightCanonical
    leftNormalizedLabels rightNormalizedLabels oldSame
    (pre:=[]) (post:=principal.edges) (by simpa only [List.nil_append] using leftSource)
  have maps : targetFirst.segments.map (plugEnd (cut).label (rhs).label).invFun=
      targetSecond.segments.map (plugEnd (cut).label (rhs).label).invFun := by
    rw [leftShape,rightShape,leftRawShape,rightRawShape,rawSame]
  have physical := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label)) maps
  simpa only [plug_decomposition_flatten] using physical
end
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}
/-- The actual incoming SourcePort case determines THIS APP parent. No
parent coordinate or desired physical finish is an input. -/
theorem OccurrenceFragment.app_incoming_parent
    (occurrence : OccurrenceFragment current g root leaf)
    (incoming : ∃label,occurrence.context=.appFn label ∨occurrence.context=.appArg label) :
    ∃ parent step stamp fn arg,current.subterm parent=some (.app stamp fn arg) ∧
      leaf=parent++[step] ∧(step=.fn ∨step=.arg) ∧
      SourceDeparture (.app stamp fn arg) step
        (sourceEdge occurrence.environment occurrence.context occurrence.term).fromPort := by
  rcases occurrence with ⟨sub,env,ctx,atSite,fragment⟩
  rcases atSite.last_departure with ⟨_,external⟩|⟨parent,step,term,split,lookup,role⟩
  · rcases incoming with ⟨label,equal|equal⟩ <;> cases external.symm.trans equal
  · have sourceFrom : (sourceEdge env ctx sub).fromPort=ctx := by cases sub <;> rfl
    cases role with
    | fn => exact ⟨parent,.fn,_,_,_,lookup,split,Or.inl rfl,by rw [sourceFrom];exact .fn⟩
    | arg => exact ⟨parent,.arg,_,_,_,lookup,split,Or.inr rfl,by rw [sourceFrom];exact .arg⟩
    | body => rcases incoming with ⟨label,equal|equal⟩ <;> cases equal
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
/-- A real successful lambda-context slot with an actual FN/ARG incoming
APP parent transports forward. BODY-parent and other copied endpoints remain
outside this finite subclass. Both APP parents and kept finishes are internal. -/
theorem PathSite.fan_lambda_context_same_slot_fragment_forward
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site)
    (selection : OccurrenceFragmentSelection current site.net root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (leftIncoming : ∃label,(selection leftPosition).context=.appFn label ∨(selection leftPosition).context=.appArg label)
    (rightIncoming : ∃label,(selection rightPosition).context=.appFn label ∨(selection rightPosition).context=.appArg label)
    (targetFirst : OccurrenceFragment current site.reduce root leftPosition.val)
    (targetSecond : OccurrenceFragment current site.reduce root rightPosition.val)
    (leftBranch rightBranch : Bool)
    (leftFinish : targetFirst.fragment.access.val.getLast?=
      some (site.reduce.wire (.inl ⟨.inr (.inl leftBranch),.inl ()⟩)))
    (rightFinish : targetSecond.fragment.access.val.getLast?=
      some (site.reduce.wire (.inl ⟨.inr (.inl rightBranch),.inl ()⟩))) :
    targetFirst.fragment.segments=targetSecond.fragment.segments := by
  have pieces := same_chain_representation_slot selection first second physical leftPosition rightPosition leftSlot rightSlot
  have branches := site.fan_lambda_same_slot_branches sourceMatches flow positive principal selection first second
    physical leftPosition rightPosition leftSlot rightSlot targetFirst.fragment.access targetSecond.fragment.access
    targetFirst.fragment.word targetSecond.fragment.word leftBranch rightBranch leftFinish rightFinish
  subst rightBranch
  obtain ⟨lp,lstep,la,lfn,larg,lLookup,lSplit,_lsteps,lRole⟩ := (selection leftPosition).app_incoming_parent leftIncoming
  obtain ⟨rp,rstep,ra,rfn,rarg,rLookup,rSplit,_rsteps,rRole⟩ := (selection rightPosition).app_incoming_parent rightIncoming
  let leftParentPosition : Position current.erase := ⟨lp,by rw [←LTerm.erase_subterm,lLookup];rfl⟩
  let rightParentPosition : Position current.erase := ⟨rp,by rw [←LTerm.erase_subterm,rLookup];rfl⟩
  obtain ⟨sourceLeft,sourceLeftWord,_⟩ := Matches.observation site.net sourceMatches leftParentPosition
  obtain ⟨sourceRight,sourceRightWord,_⟩ := Matches.observation site.net sourceMatches rightParentPosition
  obtain ⟨targetLeft,targetLeftWord,lu,leftShape,leftObs⟩ := Matches.observation site.reduce targetMatches leftParentPosition
  obtain ⟨targetRight,targetRightWord,ru,rightShape,rightObs⟩ := Matches.observation site.reduce targetMatches rightParentPosition
  have lErased : subtermAt current.erase lp=some (.app lfn.erase larg.erase) := by
    rw [←LTerm.erase_subterm,lLookup];rfl
  have rErased : subtermAt current.erase rp=some (.app rfn.erase rarg.erase) := by
    rw [←LTerm.erase_subterm,rLookup];rfl
  have leftTerm : lu=.app lfn.erase larg.erase := Option.some.inj (leftShape.symm.trans lErased)
  have rightTerm : ru=.app rfn.erase rarg.erase := Option.some.inj (rightShape.symm.trans rErased)
  subst lu
  subst ru
  have excluded : ∀port : Port (.op .lam),portKind (.op .lam) port≠some AccessKind.app := by
    intro port wrong
    rcases port with u|b
    · cases u;cases wrong
    · cases b <;> cases wrong
  obtain ⟨leftParent,leftParentAt⟩ := site.action_access_kept_of_kind_excluded (.fan .lam i j lt)
    targetLeft leftObs.1 excluded
  obtain ⟨rightParent,rightParentAt⟩ := site.action_access_kept_of_kind_excluded (.fan .lam i j lt)
    targetRight rightObs.1 excluded
  generalize lSourceEq : selection leftPosition=sourceFirst at pieces lRole
  generalize rSourceEq : selection rightPosition=sourceSecond at pieces rRole
  rcases sourceFirst with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetFirst with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceSecond with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetSecond with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact lsource.fan_kept_parent_copied_context_forward site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget lRole rRole sourceLeft sourceRight targetLeft targetRight
    (by rw [sourceLeftWord];exact lSplit) (by rw [sourceRightWord];exact rSplit)
    (by rw [targetLeftWord];exact lSplit) (by rw [targetRightWord];exact rSplit)
    leftParent rightParent leftParentAt rightParentAt leftBranch leftFinish rightFinish pieces

/-- Explicit source Joint is a conditional IH, never an asserted fixture truth. -/
theorem PathSite.fan_lambda_context_joint_same_slot_fragment_forward
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site)
    (closed : Closed current.erase) (selection : OccurrenceFragmentSelection current site.net root)
    (joint : JointRepresentation closed selection)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (iso : ChainIncidenceIsomorphic (chainSyntaxIncidence current closed left) (chainSyntaxIncidence current closed right))
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (leftIncoming : ∃label,(selection leftPosition).context=.appFn label ∨(selection leftPosition).context=.appArg label)
    (rightIncoming : ∃label,(selection rightPosition).context=.appFn label ∨(selection rightPosition).context=.appArg label)
    (targetFirst : OccurrenceFragment current site.reduce root leftPosition.val)
    (targetSecond : OccurrenceFragment current site.reduce root rightPosition.val)
    (leftBranch rightBranch : Bool)
    (leftFinish : targetFirst.fragment.access.val.getLast?=
      some (site.reduce.wire (.inl ⟨.inr (.inl leftBranch),.inl ()⟩)))
    (rightFinish : targetSecond.fragment.access.val.getLast?=
      some (site.reduce.wire (.inl ⟨.inr (.inl rightBranch),.inl ()⟩))) :
    targetFirst.fragment.segments=targetSecond.fragment.segments := by
  exact site.fan_lambda_context_same_slot_fragment_forward sourceMatches targetMatches flow positive principal
    selection first second ((joint.1 first second).mpr iso) leftPosition rightPosition leftSlot rightSlot
    leftIncoming rightIncoming targetFirst targetSecond leftBranch rightBranch leftFinish rightFinish
end
end Lamping.AG
#print axioms Lamping.AG.SourceEdgeFragment.fan_kept_parent_copied_context_forward
#print axioms Lamping.AG.OccurrenceFragment.app_incoming_parent
#print axioms Lamping.AG.PathSite.fan_lambda_context_same_slot_fragment_forward
#print axioms Lamping.AG.PathSite.fan_lambda_context_joint_same_slot_fragment_forward
