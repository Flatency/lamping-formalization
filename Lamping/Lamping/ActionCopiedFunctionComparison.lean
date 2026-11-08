import Lamping.Lamping.ActionCopiedFunctionCuts
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.croAction Op.app i j lt) V) site.closed
private abbrev appCroRight (i j : Nat) (lt : i<j) := (Schema.croAction Op.app i j lt).right.net
local notation "rhs" => appCroRight i j lt
local notation "functionSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "exitPivot" => (Sum.inr (Sum.inl (Sum.inr (Sum.inl ()))) : Endpoint cut)
local notation "activeAux" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) (Sum.inr ())) : Endpoint site.net)

/-- Whole physical-piece comparison in the copied-function/kept-terminal
class. Both normalizations are constructed from actual parent/child paths. -/
theorem SourceEdgeFragment.cro_copied_function_kept_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {leftEdge rightEdge : SourceEdge} {p q : Path}
    (sourceLeft : SourceEdgeFragment current site.net root leftEdge p)
    (targetLeft : SourceEdgeFragment current site.reduce root leftEdge p)
    (sourceRight : SourceEdgeFragment current site.net root rightEdge q)
    (targetRight : SourceEdgeFragment current site.reduce root rightEdge q)
    (leftRole : SourceDeparture leftTerm .fn leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm .fn rightEdge.fromPort)
    (oldParentLeft oldParentRight : RootAccess site.net root)
    (newParentLeft newParentRight : RootAccess site.reduce root)
    (oldWordLeft : p=accessWord site.net oldParentLeft.val++[.fn])
    (oldWordRight : q=accessWord site.net oldParentRight.val++[.fn])
    (newWordLeft : p=accessWord site.reduce newParentLeft.val++[.fn])
    (newWordRight : q=accessWord site.reduce newParentRight.val++[.fn])
    (parentLeftAt : newParentLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (parentRightAt : newParentRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (leftNode rightNode : K) (leftPort : Port (kept leftNode).sort) (rightPort : Port (kept rightNode).sort)
    (leftEnd : targetLeft.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftNode,leftPort⟩)))
    (rightEnd : targetRight.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightNode,rightPort⟩))) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetLeft.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetRight.access.property.1.1
  obtain ⟨leftRaw,leftOld,leftSeam,leftShape,leftSource,leftRelation,leftPieceLabels⟩ :=
    sourceLeft.cro_copied_function_kept_cut site flow root positive sourceMatches targetMatches principal
      targetLeft leftRole oldParentLeft newParentLeft oldWordLeft newWordLeft parentLeftAt leftNode leftPort leftEnd leftLabels
  obtain ⟨rightRaw,rightOld,rightSeam,rightShape,rightSource,rightRelation,rightPieceLabels⟩ :=
    sourceRight.cro_copied_function_kept_cut site flow root positive sourceMatches targetMatches principal
      targetRight rightRole oldParentRight newParentRight oldWordRight newWordRight parentRightAt rightNode rightPort rightEnd rightLabels
  constructor
  · intro pieces
    have maps := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label).invFun) pieces
    dsimp only at maps
    rw [leftShape,rightShape] at maps
    have tails := (List.cons.inj (List.cons.inj maps).2).2
    have old : site.outsideEnd exitPivot::leftOld=site.outsideEnd exitPivot::rightOld :=
      leftRelation.fixed_source_unique_of_eq site rightRelation (by rw [tails])
    rw [leftSource,rightSource,(List.cons.inj old).2]
  · intro pieces
    have oldWords := leftSource.symm.trans (pieces.trans rightSource)
    have tails := (List.cons.inj (List.append_cancel_left oldWords)).2
    have raw := leftRelation.unary_target_unique_of_labels site (by intro h;cases h)
      rightRelation leftPieceLabels rightPieceLabels (by rw [tails])
    have maps : targetLeft.segments.map (plugEnd (cut).label (rhs).label).invFun=
        targetRight.segments.map (plugEnd (cut).label (rhs).label).invFun := by
      rw [leftShape,rightShape,(List.cons.inj raw).2]
    have actual := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label)) maps
    simpa only [plug_decomposition_flatten] using actual

end
end Lamping.AG
