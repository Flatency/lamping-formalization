import Lamping.Lamping.CopiedLambdaBodyKeptCuts
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed
private theorem fixed_ends_canonical_equality (unary : s.active≠.fan) (principal : SiteActionPrincipal site)
    (left right : List (Endpoint site.reduce)) (oldLeft oldRight : List (Endpoint site.net))
    (pre post normalizedLeft normalizedRight : List (PlugSegment cut s.right.net))
    (leftShape : left.map (plugEnd (cut).label s.right.net.label).invFun=pre++normalizedLeft++post)
    (rightShape : right.map (plugEnd (cut).label s.right.net.label).invFun=pre++normalizedRight++post)
    (leftRelation : ActionCanonicalBlocks site principal normalizedLeft oldLeft)
    (rightRelation : ActionCanonicalBlocks site principal normalizedRight oldRight)
    {a b c d : Context} (leftLabels : PlugLabelling cut s.right.net normalizedLeft a b)
    (rightLabels : PlugLabelling cut s.right.net normalizedRight c d) :
    left=right ↔oldLeft=oldRight := by
  constructor
  · intro same
    have maps := congrArg (fun xs=>xs.map (plugEnd (cut).label s.right.net.label).invFun) same
    have shapeEq := leftShape.symm.trans (maps.trans rightShape)
    simp only [List.append_assoc] at shapeEq
    have normalized : normalizedLeft=normalizedRight := List.append_cancel_right (List.append_cancel_left shapeEq)
    exact leftRelation.fixed_source_unique_of_eq site rightRelation normalized
  · intro oldEq
    have normalized := leftRelation.unary_target_unique_of_labels site unary rightRelation leftLabels rightLabels oldEq
    have maps : left.map (plugEnd (cut).label s.right.net.label).invFun=
        right.map (plugEnd (cut).label s.right.net.label).invFun := by rw [leftShape,rightShape,normalized]
    have actual := congrArg (fun xs=>xs.map (plugEnd (cut).label s.right.net.label)) maps
    simpa only [plug_decomposition_flatten] using actual
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
 theorem SourceEdgeFragment.cro_copied_lambda_body_kept_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {leftEdge rightEdge : SourceEdge} {p q : Path}
    (sourceFirst : SourceEdgeFragment current site.net root leftEdge p)
    (targetFirst : SourceEdgeFragment current site.reduce root leftEdge p)
    (sourceSecond : SourceEdgeFragment current site.net root rightEdge q)
    (targetSecond : SourceEdgeFragment current site.reduce root rightEdge q)
    (leftRole : SourceDeparture leftTerm .body leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm .body rightEdge.fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[.body])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[.body])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[.body])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[.body])
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (leftNode rightNode : K) (leftPort : Port (kept leftNode).sort) (rightPort : Port (kept rightNode).sort)
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftNode,leftPort⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightNode,rightPort⟩))) :
    targetFirst.segments=targetSecond.segments ↔sourceFirst.segments=sourceSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨leftTail,leftOld,seamLeft,_,leftShape,leftRelation,leftPieceLabels⟩ :=
    sourceFirst.cro_copied_lambda_body_kept_cut site flow root positive sourceMatches targetMatches principal targetFirst
      leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord leftParentAt leftNode leftPort leftEndAt leftLabels
  obtain ⟨rightTail,rightOld,seamRight,_,rightShape,rightRelation,rightPieceLabels⟩ :=
    sourceSecond.cro_copied_lambda_body_kept_cut site flow root positive sourceMatches targetMatches principal targetSecond
      rightRole sourceRight targetRight sourceRightWord targetRightWord rightParentAt rightNode rightPort rightEndAt rightLabels
  apply fixed_ends_canonical_equality site (by intro h;cases h) principal targetFirst.segments targetSecond.segments
    sourceFirst.segments sourceSecond.segments
    [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩)]
    []
    (.inl (.inr (.inl (.inr (.inr true))))::leftTail)
    (.inl (.inr (.inl (.inr (.inr true))))::rightTail)
    _ _ leftRelation rightRelation leftPieceLabels rightPieceLabels
  · simpa only [List.cons_append,List.nil_append,List.append_nil] using leftShape
  · simpa only [List.cons_append,List.nil_append,List.append_nil] using rightShape
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
 theorem SourceEdgeFragment.bra_copied_lambda_body_kept_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {leftEdge rightEdge : SourceEdge} {p q : Path}
    (sourceFirst : SourceEdgeFragment current site.net root leftEdge p)
    (targetFirst : SourceEdgeFragment current site.reduce root leftEdge p)
    (sourceSecond : SourceEdgeFragment current site.net root rightEdge q)
    (targetSecond : SourceEdgeFragment current site.reduce root rightEdge q)
    (leftRole : SourceDeparture leftTerm .body leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm .body rightEdge.fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[.body])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[.body])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[.body])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[.body])
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (leftNode rightNode : K) (leftPort : Port (kept leftNode).sort) (rightPort : Port (kept rightNode).sort)
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftNode,leftPort⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightNode,rightPort⟩))) :
    targetFirst.segments=targetSecond.segments ↔sourceFirst.segments=sourceSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨leftTail,leftOld,seamLeft,_,leftShape,leftRelation,leftPieceLabels⟩ :=
    sourceFirst.bra_copied_lambda_body_kept_cut site flow root positive sourceMatches targetMatches principal targetFirst
      leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord leftParentAt leftNode leftPort leftEndAt leftLabels
  obtain ⟨rightTail,rightOld,seamRight,_,rightShape,rightRelation,rightPieceLabels⟩ :=
    sourceSecond.bra_copied_lambda_body_kept_cut site flow root positive sourceMatches targetMatches principal targetSecond
      rightRole sourceRight targetRight sourceRightWord targetRightWord rightParentAt rightNode rightPort rightEndAt rightLabels
  apply fixed_ends_canonical_equality site (by intro h;cases h) principal targetFirst.segments targetSecond.segments
    sourceFirst.segments sourceSecond.segments
    [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩)]
    []
    (.inl (.inr (.inl (.inr (.inr true))))::leftTail)
    (.inl (.inr (.inl (.inr (.inr true))))::rightTail)
    _ _ leftRelation rightRelation leftPieceLabels rightPieceLabels
  · simpa only [List.cons_append,List.nil_append,List.append_nil] using leftShape
  · simpa only [List.cons_append,List.nil_append,List.append_nil] using rightShape
end

end Lamping.AG
