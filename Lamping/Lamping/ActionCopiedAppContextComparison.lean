import Lamping.Lamping.ActionCopiedAppContextCuts
import Lamping.Lamping.KeptParentCopiedBindingComparison
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
/- Compare real reader-normalized pieces by the existing generic proof.
The exposed helper's proof is shared; no second generic induction occurs. -/
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction .app i j lt) kept (B:=B) (W:=W) (V:=V))

theorem SourceEdgeFragment.cro_kept_parent_copied_app_context_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
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
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩))) :
    targetFirst.segments=targetSecond.segments ↔sourceFirst.segments=sourceSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨lp,leftRaw,ls,lo,leftOldLast,leftNewLast,leftShape,leftRelation,leftPieceLabels⟩ :=
    sourceFirst.cro_kept_parent_copied_app_context_cut site flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord leftParent.1 leftParent.2
      leftParentAt leftEndAt leftLabels
  obtain ⟨rp,rightRaw,rs,ro,rightOldLast,rightNewLast,rightShape,rightRelation,rightPieceLabels⟩ :=
    sourceSecond.cro_kept_parent_copied_app_context_cut site flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord rightParent.1 rightParent.2
      rightParentAt rightEndAt rightLabels
  exact reader_piece_equality site (by intro wrong;cases wrong) sourceMatches targetMatches principal
    sourceFirst targetFirst sourceSecond targetSecond leftRole rightRole
    sourceLeft sourceRight targetLeft targetRight sourceLeftWord sourceRightWord targetLeftWord targetRightWord
    lp rp leftRaw rightRaw _ leftOldLast rightOldLast leftNewLast rightNewLast
    leftShape rightShape leftRelation rightRelation leftPieceLabels rightPieceLabels
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction .app i j lt) kept (B:=B) (W:=W) (V:=V))

theorem SourceEdgeFragment.bra_kept_parent_copied_app_context_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
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
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩))) :
    targetFirst.segments=targetSecond.segments ↔sourceFirst.segments=sourceSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨lp,leftRaw,ls,lo,leftOldLast,leftNewLast,leftShape,leftRelation,leftPieceLabels⟩ :=
    sourceFirst.bra_kept_parent_copied_app_context_cut site flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord leftParent.1 leftParent.2
      leftParentAt leftEndAt leftLabels
  obtain ⟨rp,rightRaw,rs,ro,rightOldLast,rightNewLast,rightShape,rightRelation,rightPieceLabels⟩ :=
    sourceSecond.bra_kept_parent_copied_app_context_cut site flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord rightParent.1 rightParent.2
      rightParentAt rightEndAt rightLabels
  exact reader_piece_equality site (by intro wrong;cases wrong) sourceMatches targetMatches principal
    sourceFirst targetFirst sourceSecond targetSecond leftRole rightRole
    sourceLeft sourceRight targetLeft targetRight sourceLeftWord sourceRightWord targetLeftWord targetRightWord
    lp rp leftRaw rightRaw _ leftOldLast rightOldLast leftNewLast rightNewLast
    leftShape rightShape leftRelation rightRelation leftPieceLabels rightPieceLabels
end
end Lamping.AG

#print axioms Lamping.AG.SourceEdgeFragment.cro_kept_parent_copied_app_context_equality
#print axioms Lamping.AG.SourceEdgeFragment.bra_kept_parent_copied_app_context_equality
