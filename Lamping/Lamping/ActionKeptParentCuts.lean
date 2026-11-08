import Lamping.Lamping.ActionKeptFragmentComparison
import Lamping.Lamping.ActionRawOutsideCut
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed
theorem SourceEdgeFragment.action_kept_parent_cut (action : IsAction s)
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {edge : SourceEdge} {position : Path}
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    {parentTerm : LTerm} {step : Step} (role : SourceDeparture parentTerm step edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[step])
    (targetWord : position=accessWord site.reduce targetParent.val++[step])
    (parentNode endNode : K) (parentPort : Port (kept parentNode).sort) (endPort : Port (kept endNode).sort)
    (parentEnd : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inl parentNode,parentPort⟩)))
    (endAt : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl endNode,endPort⟩)))
    {a b : Context} (labels : Labelling site.reduce target.access.val a b) :
    ∃ pivot : Endpoint cut,∃ seam : Context,
      sourceParent.val.getLast?=some (site.outsideEnd pivot) ∧
      targetParent.val.getLast?=some (AG.plugLeft cut s.right.net pivot) ∧
      ActionCanonicalBlocks site principal
        (Sum.inl pivot::target.segments.map (plugEnd (cut).label s.right.net.label).invFun)
        (site.outsideEnd pivot::source.segments) ∧
      PlugLabelling cut s.right.net
        (Sum.inl pivot::target.segments.map (plugEnd (cut).label s.right.net.label).invFun) seam b := by
  obtain ⟨whole,_sourceLabels,_sourceEnd⟩ := site.action_kept_canonical_access action flow root positive
    sourceMatches principal source.access target.access (source.word.trans target.word.symm)
    endNode endPort endAt labels
  obtain ⟨c,d,parentLabels⟩ := targetParent.property.1.1
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  obtain ⟨parent,_parentSourceLabels,parentLast⟩ := site.action_kept_canonical_access action flow root positive
    sourceMatches principal sourceParent targetParent parentWord parentNode parentPort parentEnd parentLabels
  let pivot : Endpoint cut := (cut).wire (.inl ⟨parentNode,parentPort⟩)
  have parentOutside : sourceParent.val.getLast?=some (site.outsideEnd pivot) := by
    change sourceParent.val.getLast?=some (site.outsideEnd ((cut).wire (.inl ⟨parentNode,parentPort⟩)))
    rw [←site.outsideEnd_wire]
    exact parentLast
  have targetOutside : targetParent.val.getLast?=some (AG.plugLeft cut s.right.net pivot) :=
    parentEnd.trans (congrArg some (plugLeft_wire cut s.right.net (.inl ⟨parentNode,parentPort⟩)))
  have rawLast : (targetParent.val.map (plugEnd (cut).label s.right.net.label).invFun).getLast?=
      some (Sum.inl pivot) := by
    rw [List.getLast?_map,targetOutside]
    exact congrArg some ((plugEnd (cut).label s.right.net.label).left_inv (.inl pivot))
  have sourceCut := (source.child_prefix sourceMatches role sourceParent sourceWord).2
  have targetCut := (target.child_prefix targetMatches role targetParent targetWord).2
  have rawSplit := congrArg (fun xs=>xs.map (plugEnd (cut).label s.right.net.label).invFun) targetCut
  simp only [List.map_append] at rawSplit
  obtain ⟨oldPiece,seam,oldSplit,relation,_sameParentLabels,pieceLabels⟩ :=
    whole.cut_at_raw_parent site parent (labels.plug_decomposition cut s.right.net) rawSplit pivot rawLast
  have samePiece : oldPiece=source.segments := List.append_cancel_left (oldSplit.symm.trans sourceCut)
  rw [samePiece] at relation
  exact ⟨pivot,seam,parentOutside,targetOutside,relation,pieceLabels⟩
end
end Lamping.AG
