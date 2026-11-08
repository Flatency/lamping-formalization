import Lamping.Lamping.KeptParentCopiedLambdaCuts
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

private theorem padded_piece_equality (unary : s.active≠.fan)
    {root : B} {current : LTerm} {leftEdge rightEdge : SourceEdge} {p q : Path}
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
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
    (lp rp : Endpoint cut) (post : List (PlugSegment cut s.right.net))
    (oldPost : List (Endpoint site.net))
    (leftOldLast : sourceLeft.val.getLast?=some (site.outsideEnd lp))
    (rightOldLast : sourceRight.val.getLast?=some (site.outsideEnd rp))
    (leftNewLast : targetLeft.val.getLast?=some (AG.plugLeft cut s.right.net lp))
    (rightNewLast : targetRight.val.getLast?=some (AG.plugLeft cut s.right.net rp))
    (leftRelation : ActionCanonicalBlocks site principal
      (Sum.inl lp::(targetFirst.segments.map (plugEnd (cut).label s.right.net.label).invFun++post))
      (site.outsideEnd lp::(sourceFirst.segments++oldPost)))
    (rightRelation : ActionCanonicalBlocks site principal
      (Sum.inl rp::(targetSecond.segments.map (plugEnd (cut).label s.right.net.label).invFun++post))
      (site.outsideEnd rp::(sourceSecond.segments++oldPost)))
    {a b c d : Context}
    (leftLabels : PlugLabelling cut s.right.net (Sum.inl lp::(targetFirst.segments.map (plugEnd (cut).label s.right.net.label).invFun++post)) a b)
    (rightLabels : PlugLabelling cut s.right.net (Sum.inl rp::(targetSecond.segments.map (plugEnd (cut).label s.right.net.label).invFun++post)) c d) :
    targetFirst.segments=targetSecond.segments ↔sourceFirst.segments=sourceSecond.segments := by
  constructor
  · intro pieces
    have parents := SourceEdgeFragment.equal_piece_parent_seams targetMatches targetFirst targetSecond
      leftRole rightRole targetLeft targetRight targetLeftWord targetRightWord pieces
    have mappedSame := Option.some.inj (leftNewLast.symm.trans (parents.trans rightNewLast))
    have pivots : lp=rp := by
      apply Sum.inl.inj
      apply (plugEnd (cut).label s.right.net.label).injective
      exact mappedSame
    subst rp
    have old := leftRelation.fixed_source_unique_of_eq site rightRelation (by rw [pieces])
    exact List.append_cancel_right (List.cons.inj old).2
  · intro pieces
    have parents := SourceEdgeFragment.equal_piece_parent_seams sourceMatches sourceFirst sourceSecond
      leftRole rightRole sourceLeft sourceRight sourceLeftWord sourceRightWord pieces
    have outsideSame := Option.some.inj (leftOldLast.symm.trans (parents.trans rightOldLast))
    have pivots : lp=rp := by
      apply Sum.inl.inj
      apply (fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition s V)).symm.injective
      exact outsideSame
    subst rp
    have raw := leftRelation.unary_target_unique_of_labels site unary rightRelation
      leftLabels rightLabels (by rw [pieces])
    have tails := (List.cons.inj raw).2
    have maps := List.append_cancel_right tails
    have actual := congrArg (fun xs=>xs.map (plugEnd (cut).label s.right.net.label)) maps
    simpa only [plug_decomposition_flatten] using actual
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))

theorem SourceEdgeFragment.cro_kept_parent_copied_lambda_equality
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
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩))) :
    targetFirst.segments=targetSecond.segments ↔sourceFirst.segments=sourceSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨lp,ls,lo,leftOldLast,leftNewLast,leftRelation,leftPieceLabels⟩ :=
    sourceFirst.cro_kept_parent_copied_lambda_cut site flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord leftParent.1 leftParent.2
      leftParentAt leftEndAt leftLabels
  obtain ⟨rp,rs,ro,rightOldLast,rightNewLast,rightRelation,rightPieceLabels⟩ :=
    sourceSecond.cro_kept_parent_copied_lambda_cut site flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord rightParent.1 rightParent.2
      rightParentAt rightEndAt rightLabels
  exact padded_piece_equality site (by intro wrong;cases wrong) sourceMatches targetMatches principal
    sourceFirst targetFirst sourceSecond targetSecond leftRole rightRole
    sourceLeft sourceRight targetLeft targetRight sourceLeftWord sourceRightWord targetLeftWord targetRightWord
    lp rp _ _ leftOldLast rightOldLast leftNewLast rightNewLast
    leftRelation rightRelation leftPieceLabels rightPieceLabels
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))

theorem SourceEdgeFragment.bra_kept_parent_copied_lambda_equality
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
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩))) :
    targetFirst.segments=targetSecond.segments ↔sourceFirst.segments=sourceSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨lp,ls,lo,leftOldLast,leftNewLast,leftRelation,leftPieceLabels⟩ :=
    sourceFirst.bra_kept_parent_copied_lambda_cut site flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord leftParent.1 leftParent.2
      leftParentAt leftEndAt leftLabels
  obtain ⟨rp,rs,ro,rightOldLast,rightNewLast,rightRelation,rightPieceLabels⟩ :=
    sourceSecond.bra_kept_parent_copied_lambda_cut site flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord rightParent.1 rightParent.2
      rightParentAt rightEndAt rightLabels
  exact padded_piece_equality site (by intro wrong;cases wrong) sourceMatches targetMatches principal
    sourceFirst targetFirst sourceSecond targetSecond leftRole rightRole
    sourceLeft sourceRight targetLeft targetRight sourceLeftWord sourceRightWord targetLeftWord targetRightWord
    lp rp _ _ leftOldLast rightOldLast leftNewLast rightNewLast
    leftRelation rightRelation leftPieceLabels rightPieceLabels
end
end Lamping.AG

