import Lamping.Lamping.CopiedLambdaBodyKeptCuts
import Lamping.Lamping.FragmentParentSeparation
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction Op.lam i j lt) kept (B:=B) (W:=W) (V:=V))
theorem SourceEdgeFragment.cro_copied_lambda_body_vs_kept_parent
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {edge : SourceEdge} {position : Path}
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm .body edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[.body])
    (targetWord : position=accessWord site.reduce targetParent.val++[.body])
    (parentFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),(Sum.inl ())⟩)))
    (endNode : K) (endPort : Port (kept endNode).sort)
    (endAt : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl endNode,endPort⟩)))
    (otherSource : SourceEdgeFragment current site.net root otherEdge otherPosition)
    (otherTarget : SourceEdgeFragment current site.reduce root otherEdge otherPosition)
    (otherRole : SourceDeparture otherTerm otherStep otherEdge.fromPort)
    (oldKeptParent : RootAccess site.net root) (newKeptParent : RootAccess site.reduce root)
    (oldKeptWord : otherPosition=accessWord site.net oldKeptParent.val++[otherStep])
    (newKeptWord : otherPosition=accessWord site.reduce newKeptParent.val++[otherStep])
    (oldKeptNode newKeptNode : K)
    (oldKeptPort : Port (kept oldKeptNode).sort) (newKeptPort : Port (kept newKeptNode).sort)
    (oldKeptFinish : oldKeptParent.val.getLast?=some (site.net.wire (.inl ⟨.inl oldKeptNode,oldKeptPort⟩)))
    (newKeptFinish : newKeptParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inl newKeptNode,newKeptPort⟩))) :
    otherSource.segments≠source.segments ∧ otherTarget.segments≠target.segments ∧
    (otherTarget.segments=target.segments ↔otherSource.segments=source.segments) := by
  obtain ⟨a,b,labels⟩ := target.access.property.1.1
  obtain ⟨rawTail,oldTail,seam,sourceShape,_targetShape,_relation,_pieceLabels⟩ :=
    source.cro_copied_lambda_body_kept_cut site flow root positive sourceMatches targetMatches principal
      target role sourceParent targetParent sourceWord targetWord parentFinish endNode endPort endAt labels
  have sourceHead : source.segments.head?=some (.inl ⟨.inr (.inr ()),.inr true⟩) := by
    rw [sourceShape];rfl
  obtain ⟨departure,otherHead⟩ := otherSource.head_node_of_parent sourceMatches otherRole
    oldKeptParent oldKeptWord (.inl oldKeptNode) oldKeptPort oldKeptFinish
  have sourceNe : otherSource.segments≠source.segments := by
    intro same
    have heads := congrArg List.head? same
    rw [otherHead,sourceHead] at heads
    have nodes := congrArg Sigma.fst (Sum.inl.inj (Option.some.inj heads))
    cases nodes
  have targetNe : otherTarget.segments≠target.segments :=
    otherTarget.ne_of_parent_nodes targetMatches target otherRole role
      newKeptParent targetParent newKeptWord targetWord (.inl newKeptNode) (.inr (.inl ()))
      newKeptPort (Sum.inl ()) newKeptFinish parentFinish (by intro h;cases h)
  exact ⟨sourceNe,targetNe,⟨fun h=>False.elim (targetNe h),fun h=>False.elim (sourceNe h)⟩⟩
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction Op.lam i j lt) kept (B:=B) (W:=W) (V:=V))
theorem SourceEdgeFragment.bra_copied_lambda_body_vs_kept_parent
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {edge : SourceEdge} {position : Path}
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm .body edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[.body])
    (targetWord : position=accessWord site.reduce targetParent.val++[.body])
    (parentFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),(Sum.inl ())⟩)))
    (endNode : K) (endPort : Port (kept endNode).sort)
    (endAt : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl endNode,endPort⟩)))
    (otherSource : SourceEdgeFragment current site.net root otherEdge otherPosition)
    (otherTarget : SourceEdgeFragment current site.reduce root otherEdge otherPosition)
    (otherRole : SourceDeparture otherTerm otherStep otherEdge.fromPort)
    (oldKeptParent : RootAccess site.net root) (newKeptParent : RootAccess site.reduce root)
    (oldKeptWord : otherPosition=accessWord site.net oldKeptParent.val++[otherStep])
    (newKeptWord : otherPosition=accessWord site.reduce newKeptParent.val++[otherStep])
    (oldKeptNode newKeptNode : K)
    (oldKeptPort : Port (kept oldKeptNode).sort) (newKeptPort : Port (kept newKeptNode).sort)
    (oldKeptFinish : oldKeptParent.val.getLast?=some (site.net.wire (.inl ⟨.inl oldKeptNode,oldKeptPort⟩)))
    (newKeptFinish : newKeptParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inl newKeptNode,newKeptPort⟩))) :
    otherSource.segments≠source.segments ∧ otherTarget.segments≠target.segments ∧
    (otherTarget.segments=target.segments ↔otherSource.segments=source.segments) := by
  obtain ⟨a,b,labels⟩ := target.access.property.1.1
  obtain ⟨rawTail,oldTail,seam,sourceShape,_targetShape,_relation,_pieceLabels⟩ :=
    source.bra_copied_lambda_body_kept_cut site flow root positive sourceMatches targetMatches principal
      target role sourceParent targetParent sourceWord targetWord parentFinish endNode endPort endAt labels
  have sourceHead : source.segments.head?=some (.inl ⟨.inr (.inr ()),.inr true⟩) := by
    rw [sourceShape];rfl
  obtain ⟨departure,otherHead⟩ := otherSource.head_node_of_parent sourceMatches otherRole
    oldKeptParent oldKeptWord (.inl oldKeptNode) oldKeptPort oldKeptFinish
  have sourceNe : otherSource.segments≠source.segments := by
    intro same
    have heads := congrArg List.head? same
    rw [otherHead,sourceHead] at heads
    have nodes := congrArg Sigma.fst (Sum.inl.inj (Option.some.inj heads))
    cases nodes
  have targetNe : otherTarget.segments≠target.segments :=
    otherTarget.ne_of_parent_nodes targetMatches target otherRole role
      newKeptParent targetParent newKeptWord targetWord (.inl newKeptNode) (.inr (.inl ()))
      newKeptPort (Sum.inl ()) newKeptFinish parentFinish (by intro h;cases h)
  exact ⟨sourceNe,targetNe,⟨fun h=>False.elim (targetNe h),fun h=>False.elim (sourceNe h)⟩⟩
end
end Lamping.AG
