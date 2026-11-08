import Lamping.Lamping.ActionPendingCanonicalAccess
import Lamping.Lamping.ActionKeptFragmentComparison
import Lamping.Lamping.FragmentParentSeparation
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))

/-- Actual copied-versus-kept parent separation, with no terminal restriction.
Both OLD finishes follow internally from the SAME actual parent accesses. -/
theorem SourceEdgeFragment.cro_copied_app_parent_vs_kept_parent
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (otherSource : SourceEdgeFragment current site.net root otherEdge otherPosition)
    (otherTarget : SourceEdgeFragment current site.reduce root otherEdge otherPosition)
    (role : SourceDeparture parentTerm step edge.fromPort)
    (otherRole : SourceDeparture otherTerm otherStep otherEdge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (otherSourceParent : RootAccess site.net root) (otherTargetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[step])
    (targetWord : position=accessWord site.reduce targetParent.val++[step])
    (otherSourceWord : otherPosition=accessWord site.net otherSourceParent.val++[otherStep])
    (otherTargetWord : otherPosition=accessWord site.reduce otherTargetParent.val++[otherStep])
    (copiedFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (keptNode : K) (keptPort : Port (kept keptNode).sort)
    (keptFinish : otherTargetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inl keptNode,keptPort⟩))) :
    source.segments≠otherSource.segments ∧target.segments≠otherTarget.segments ∧
      (target.segments=otherTarget.segments ↔source.segments=otherSource.segments) := by
  obtain ⟨a,b,parentLabels⟩ := targetParent.property.1.1
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  obtain ⟨pending,_relation,_oldLabels,oldCopiedFinish,_shape⟩ :=
    site.cro_aux_canonical_access flow root positive sourceMatches principal
      sourceParent targetParent parentWord false copiedFinish parentLabels
  obtain ⟨c,d,otherLabels⟩ := otherTargetParent.property.1.1
  have otherWord : accessWord site.net otherSourceParent.val=accessWord site.reduce otherTargetParent.val :=
    List.append_cancel_right (otherSourceWord.symm.trans otherTargetWord)
  obtain ⟨_otherRelation,_otherOldLabels,oldKeptFinish⟩ := site.action_kept_canonical_access
    (.cro .app i j lt) flow root positive sourceMatches principal otherSourceParent otherTargetParent
      otherWord keptNode keptPort keptFinish otherLabels
  have oldDifferent : source.segments≠otherSource.segments :=
    source.ne_of_parent_nodes sourceMatches otherSource role otherRole sourceParent otherSourceParent
      sourceWord otherSourceWord (.inr (.inr ())) (.inl keptNode) appCtx keptPort
      oldCopiedFinish oldKeptFinish (by intro impossible;cases impossible)
  have newDifferent : target.segments≠otherTarget.segments :=
    target.ne_of_parent_nodes targetMatches otherTarget role otherRole targetParent otherTargetParent
      targetWord otherTargetWord (.inr (.inl ())) (.inl keptNode) appCtx keptPort
      copiedFinish keptFinish (by intro impossible;cases impossible)
  exact ⟨oldDifferent,newDifferent,⟨fun same=>(newDifferent same).elim,fun same=>(oldDifferent same).elim⟩⟩
end
#print axioms SourceEdgeFragment.cro_copied_app_parent_vs_kept_parent
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))

/-- Actual copied-versus-kept parent separation, with no terminal restriction.
Both OLD finishes follow internally from the SAME actual parent accesses. -/
theorem SourceEdgeFragment.bra_copied_app_parent_vs_kept_parent
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (otherSource : SourceEdgeFragment current site.net root otherEdge otherPosition)
    (otherTarget : SourceEdgeFragment current site.reduce root otherEdge otherPosition)
    (role : SourceDeparture parentTerm step edge.fromPort)
    (otherRole : SourceDeparture otherTerm otherStep otherEdge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (otherSourceParent : RootAccess site.net root) (otherTargetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[step])
    (targetWord : position=accessWord site.reduce targetParent.val++[step])
    (otherSourceWord : otherPosition=accessWord site.net otherSourceParent.val++[otherStep])
    (otherTargetWord : otherPosition=accessWord site.reduce otherTargetParent.val++[otherStep])
    (copiedFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (keptNode : K) (keptPort : Port (kept keptNode).sort)
    (keptFinish : otherTargetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inl keptNode,keptPort⟩))) :
    source.segments≠otherSource.segments ∧target.segments≠otherTarget.segments ∧
      (target.segments=otherTarget.segments ↔source.segments=otherSource.segments) := by
  obtain ⟨a,b,parentLabels⟩ := targetParent.property.1.1
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  obtain ⟨pending,_relation,_oldLabels,oldCopiedFinish,_shape⟩ :=
    site.bra_aux_canonical_access flow root positive sourceMatches principal
      sourceParent targetParent parentWord false copiedFinish parentLabels
  obtain ⟨c,d,otherLabels⟩ := otherTargetParent.property.1.1
  have otherWord : accessWord site.net otherSourceParent.val=accessWord site.reduce otherTargetParent.val :=
    List.append_cancel_right (otherSourceWord.symm.trans otherTargetWord)
  obtain ⟨_otherRelation,_otherOldLabels,oldKeptFinish⟩ := site.action_kept_canonical_access
    (.bra .app i j lt) flow root positive sourceMatches principal otherSourceParent otherTargetParent
      otherWord keptNode keptPort keptFinish otherLabels
  have oldDifferent : source.segments≠otherSource.segments :=
    source.ne_of_parent_nodes sourceMatches otherSource role otherRole sourceParent otherSourceParent
      sourceWord otherSourceWord (.inr (.inr ())) (.inl keptNode) appCtx keptPort
      oldCopiedFinish oldKeptFinish (by intro impossible;cases impossible)
  have newDifferent : target.segments≠otherTarget.segments :=
    target.ne_of_parent_nodes targetMatches otherTarget role otherRole targetParent otherTargetParent
      targetWord otherTargetWord (.inr (.inl ())) (.inl keptNode) appCtx keptPort
      copiedFinish keptFinish (by intro impossible;cases impossible)
  exact ⟨oldDifferent,newDifferent,⟨fun same=>(newDifferent same).elim,fun same=>(oldDifferent same).elim⟩⟩
end
#print axioms SourceEdgeFragment.bra_copied_app_parent_vs_kept_parent
end Lamping.AG
