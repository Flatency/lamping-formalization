import Lamping.Lamping.ActionKeptParentCuts
import Lamping.Lamping.ActualFragmentFanUniqueness
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {op : Op} {i j : Nat} {lt : i<j}
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite (Schema.fanAction op i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "s" => Schema.fanAction op i j lt
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed
private theorem outside_injective : Function.Injective site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition s V)
  have mapped := congrArg split same
  change split (split.invFun (.inl e))=split (split.invFun (.inl f)) at mapped
  simpa only [split.right_inv,Sum.inl.injEq] using mapped

private theorem plugLeft_injective : Function.Injective (AG.plugLeft cut (fanRight op i j)) := by
  intro e f same
  have mapped := congrArg (plugEnd (cut).label (fanRight op i j).label).invFun same
  change (plugEnd (cut).label (fanRight op i j).label).invFun ((plugEnd (cut).label (fanRight op i j).label) (.inl e))=
    (plugEnd (cut).label (fanRight op i j).label).invFun ((plugEnd (cut).label (fanRight op i j).label) (.inl f)) at mapped
  rw [Bij.left_inv,Bij.left_inv] at mapped
  exact Sum.inl.inj mapped

theorem SourceEdgeFragment.fan_kept_piece_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {firstEdge secondEdge : SourceEdge} {p q : Path}
    (sourceFirst : SourceEdgeFragment current site.net root firstEdge p)
    (targetFirst : SourceEdgeFragment current site.reduce root firstEdge p)
    (sourceSecond : SourceEdgeFragment current site.net root secondEdge q)
    (targetSecond : SourceEdgeFragment current site.reduce root secondEdge q)
    {leftTerm rightTerm : LTerm} {leftStep rightStep : Step}
    (leftRole : SourceDeparture leftTerm leftStep firstEdge.fromPort)
    (rightRole : SourceDeparture rightTerm rightStep secondEdge.fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[leftStep])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[rightStep])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[leftStep])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[rightStep])
    (leftParent rightParent leftEnd rightEnd : NodePort signature K kept)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftParent.1,leftParent.2⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightParent.1,rightParent.2⟩)))
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftEnd.1,leftEnd.2⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightEnd.1,rightEnd.2⟩))) :
    targetFirst.segments=targetSecond.segments ↔sourceFirst.segments=sourceSecond.segments := by
  let action : IsAction (Schema.fanAction op i j lt) := .fan op i j lt
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨lp,ls,leftOldLast,leftNewLast,leftRelation,leftPieceLabels⟩ :=
    sourceFirst.action_kept_parent_cut site action flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord leftParent.1 leftEnd.1
      leftParent.2 leftEnd.2 leftParentAt leftEndAt leftLabels
  obtain ⟨rp,rs,rightOldLast,rightNewLast,rightRelation,rightPieceLabels⟩ :=
    sourceSecond.action_kept_parent_cut site action flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord rightParent.1 rightEnd.1
      rightParent.2 rightEnd.2 rightParentAt rightEndAt rightLabels
  constructor
  · intro pieces
    have parentSame := SourceEdgeFragment.equal_piece_parent_seams targetMatches targetFirst targetSecond
      leftRole rightRole targetLeft targetRight targetLeftWord targetRightWord pieces
    have mappedSame := Option.some.inj (leftNewLast.symm.trans (parentSame.trans rightNewLast))
    have pivots := plugLeft_injective site mappedSame
    subst rp
    rw [pieces] at leftRelation
    exact (List.cons.inj (leftRelation.fixed_source_unique site rightRelation)).2
  · intro pieces
    have parentSame := SourceEdgeFragment.equal_piece_parent_seams sourceMatches sourceFirst sourceSecond
      leftRole rightRole sourceLeft sourceRight sourceLeftWord sourceRightWord pieces
    have outsideSame := Option.some.inj (leftOldLast.symm.trans (parentSame.trans rightOldLast))
    have pivots := outside_injective site outsideSame
    subst rp
    obtain ⟨parentInput,parentOutput,parentLabels⟩ := targetLeft.property.1.1
    have parentWord : accessWord site.net sourceLeft.val=accessWord site.reduce targetLeft.val :=
      List.append_cancel_right (sourceLeftWord.symm.trans targetLeftWord)
    obtain ⟨_parentRelation,_parentSourceLabels,parentFinish⟩ :=
      site.action_kept_canonical_access action flow root positive sourceMatches principal
        sourceLeft targetLeft parentWord leftParent.1 leftParent.2 leftParentAt parentLabels
    rw [←pieces] at rightRelation
    obtain ⟨_actualPivot,rawSame⟩ := sourceFirst.fan_target_unique_of_kept_parent_fragment site
      sourceMatches leftRole sourceLeft sourceLeftWord leftParent.1 leftParent.2 parentFinish
      lp leftOldLast leftRelation rightRelation leftPieceLabels rightPieceLabels
    have maps := (List.cons.inj rawSame).2
    change targetFirst.segments.map (plugEnd (cut).label (fanRight op i j).label).invFun=
      targetSecond.segments.map (plugEnd (cut).label (fanRight op i j).label).invFun at maps
    have physical := congrArg (fun xs=>xs.map (plugEnd (cut).label (fanRight op i j).label)) maps
    simp only [List.map_map,Function.comp_def,Bij.right_inv] at physical
    change targetFirst.segments.map id=targetSecond.segments.map id at physical
    simpa only [List.map_id] using physical
end
end Lamping.AG
