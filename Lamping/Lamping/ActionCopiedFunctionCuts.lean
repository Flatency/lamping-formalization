import Lamping.Lamping.ActionRawOutsideCut
import Lamping.Lamping.ActionFunctionPadding
import Lamping.Lamping.ActionCopiedFunctionPrefixes
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

/-- The actual copied APP parent and kept child terminal determine both
normalizations. The old split is a conclusion, not an oracle supplied by
the caller. The seam is cut from this same whole target labelling. -/
theorem SourceEdgeFragment.cro_copied_function_kept_cut
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {edge : SourceEdge} {position : Path}
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm .fn edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[.fn])
    (targetWord : position=accessWord site.reduce targetParent.val++[.fn])
    (parentFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (endNode : K) (endPort : Port (kept endNode).sort)
    (endAt : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl endNode,endPort⟩)))
    {a b : Context} (wholeLabels : Labelling site.reduce target.access.val a b) :
    ∃ rawTail oldTail seam,
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=
        functionSegment::Sum.inl exitPivot::rawTail ∧
      source.segments=reverseEdges principal.edges++activeAux::oldTail ∧
      ActionCanonicalBlocks site principal (Sum.inl exitPivot::rawTail)
        (site.outsideEnd exitPivot::oldTail) ∧
      PlugLabelling cut rhs (Sum.inl exitPivot::rawTail) seam b := by
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨pieceInput,prefixLabels,pieceLabels⟩ := target.assignments a b wholeLabels
  obtain ⟨rawTail,targetShape,_tailLabels⟩ := unary_copied_function_fragment cut .cro
    (Bij.refl _) i (j-1) targetMatches target role targetParent targetWord parentFinish pieceLabels
  change List (PlugSegment cut rhs) at rawTail
  change target.segments.map (plugEnd (cut).label (rhs).label).invFun=
    functionSegment::Sum.inl exitPivot::rawTail at targetShape
  obtain ⟨whole,_sourceWholeLabels,_sourceEnd⟩ := site.action_kept_canonical_access (.cro .app i j lt)
    flow root positive sourceMatches principal source.access target.access
    (source.word.trans target.word.symm) endNode endPort endAt wholeLabels
  obtain ⟨c,d,parentLabels⟩ := targetParent.property.1.1
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  have parent := site.cro_function_padding_access flow root positive sourceMatches principal
    sourceParent targetParent parentWord parentFinish parentLabels
  have rawSplit : target.access.val.map (plugEnd (cut).label (rhs).label).invFun=
      (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
        [functionSegment,Sum.inl exitPivot])++rawTail := by
    rw [targetCut.2,List.map_append,targetShape]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  have parentLast : (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
      [functionSegment,Sum.inl exitPivot]).getLast?=some (Sum.inl exitPivot) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨oldTail,seam,oldSplit,relation,_actualParentLabels,actualPieceLabels⟩ :=
    whole.cut_at_raw_parent site parent (wholeLabels.plug_decomposition cut rhs) rawSplit exitPivot parentLast
  have sourceCut := source.child_prefix sourceMatches role sourceParent sourceWord
  have sourceShape : source.segments=reverseEdges principal.edges++activeAux::oldTail := by
    apply List.append_cancel_left (as:=sourceParent.val)
    rw [←sourceCut.2,oldSplit]
    simp only [List.append_assoc,List.singleton_append]
  exact ⟨rawTail,oldTail,seam,targetShape,sourceShape,relation,actualPieceLabels⟩

end
end Lamping.AG
