/- Actual unary copied-APP context reader cuts. The q=false pending reader
has two RHS segments; the supplied whole assignment yields the exact parent
and suffix seam at the actual kept-parent ordinal. No old split is a premise. -/
import Lamping.Lamping.ActionKeptParentCuts
import Lamping.Lamping.ActionCopiedBindingFragmentCuts
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "s" => Schema.croAction Op.app i j lt
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed
private abbrev keptCopiedAppCroRight (i j : Nat) (lt : i<j) := (Schema.croAction Op.app i j lt).right.net
local notation "rhs" => keptCopiedAppCroRight i j lt

theorem SourceEdgeFragment.cro_kept_parent_copied_app_context_cut
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {edge : SourceEdge} {position : Path}
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm step edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[step])
    (targetWord : position=accessWord site.reduce targetParent.val++[step])
    (parentNode : K) (parentPort : Port (kept parentNode).sort)
    (parentEnd : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inl parentNode,parentPort⟩)))
    (endAt : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    {a b : Context} (labels : Labelling site.reduce target.access.val a b) :
    ∃ pivot : Endpoint cut,∃ rawPiece : List (PlugSegment cut rhs),∃ seam output : Context,
      sourceParent.val.getLast?=some (site.outsideEnd pivot) ∧
      targetParent.val.getLast?=some (AG.plugLeft cut rhs pivot) ∧
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=rawPiece++
        [.inr (.inr (.inl (.inr false))),.inr (.inl ⟨.inr false,.inr ()⟩)] ∧
      ActionCanonicalBlocks site principal (Sum.inl pivot::rawPiece)
        (site.outsideEnd pivot::source.segments) ∧
      PlugLabelling cut rhs (Sum.inl pivot::rawPiece) seam output := by
  obtain ⟨pending,whole,_sourceLabels,_sourceEnd,trimmed⟩ :=
    site.cro_aux_canonical_access flow root positive sourceMatches principal source.access target.access
      (source.word.trans target.word.symm) false endAt labels
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨middle,assignment,_pieceLabels⟩ := target.assignments a b labels
  rw [targetCut.1] at assignment
  have parentLabels : Labelling site.reduce targetParent.val a middle := by
    rcases assignment with ⟨empty,_⟩ | actual
    · have head := targetParent.property.2.1;rw [empty] at head;cases head
    · exact actual
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  obtain ⟨parent,_parentLabels,parentFinish⟩ :=
    site.action_kept_canonical_access (.cro .app i j lt) flow root positive sourceMatches principal
      sourceParent targetParent parentWord parentNode parentPort parentEnd parentLabels
  let pivot : Endpoint cut := (cut).wire (.inl ⟨parentNode,parentPort⟩)
  have oldLast : sourceParent.val.getLast?=some (site.outsideEnd pivot) := by
    change sourceParent.val.getLast?=some (site.outsideEnd ((cut).wire (.inl ⟨parentNode,parentPort⟩)))
    rw [←site.outsideEnd_wire];exact parentFinish
  have newLast : targetParent.val.getLast?=some (AG.plugLeft cut rhs pivot) :=
    parentEnd.trans (congrArg some (plugLeft_wire cut rhs (.inl ⟨parentNode,parentPort⟩)))
  have rawLast : (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun).getLast?=
      some (Sum.inl pivot) := by
    rw [List.getLast?_map,newLast]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl pivot))
  obtain ⟨initial,parentShape⟩ := List.getLast?_eq_some_iff.mp rawLast
  have untrimmed : (initial++[Sum.inl pivot])++
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=pending.pre++
        [.inr (.inr (.inl (.inr false))),.inr (.inl ⟨.inr false,.inr ()⟩)] := by
    rw [←parentShape,←List.map_append,←targetCut.2]
    exact trimmed
  obtain ⟨rawPiece,prefixSplit,pieceSplit⟩ := trim_after_literal_pivot initial
    (target.segments.map (plugEnd (cut).label (rhs).label).invFun) pending.pre (Sum.inl pivot)
    (.inr (.inr (.inl (.inr false)))) (.inr (.inl ⟨.inr false,.inr ()⟩))
    untrimmed (by intro wrong;cases wrong) (by intro wrong;cases wrong)
  have rawSplit : pending.pre=
      targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++rawPiece := by
    rw [parentShape];exact prefixSplit
  obtain ⟨oldPiece,seam,oldSplit,relation,_sameParentLabels,pieceLabels⟩ :=
    whole.cut_at_raw_parent site parent pending.prefixPath.labelling rawSplit pivot rawLast
  have sourceCut := (source.child_prefix sourceMatches role sourceParent sourceWord).2
  have samePiece : oldPiece=source.segments := List.append_cancel_left (oldSplit.symm.trans sourceCut)
  rw [samePiece] at relation
  exact ⟨pivot,rawPiece,seam,pending.middle,oldLast,newLast,pieceSplit,relation,pieceLabels⟩
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "s" => Schema.braAction Op.app i j lt
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed
private abbrev keptCopiedAppBraRight (i j : Nat) (lt : i<j) := (Schema.braAction Op.app i j lt).right.net
local notation "rhs" => keptCopiedAppBraRight i j lt

theorem SourceEdgeFragment.bra_kept_parent_copied_app_context_cut
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {edge : SourceEdge} {position : Path}
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm step edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[step])
    (targetWord : position=accessWord site.reduce targetParent.val++[step])
    (parentNode : K) (parentPort : Port (kept parentNode).sort)
    (parentEnd : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inl parentNode,parentPort⟩)))
    (endAt : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    {a b : Context} (labels : Labelling site.reduce target.access.val a b) :
    ∃ pivot : Endpoint cut,∃ rawPiece : List (PlugSegment cut rhs),∃ seam output : Context,
      sourceParent.val.getLast?=some (site.outsideEnd pivot) ∧
      targetParent.val.getLast?=some (AG.plugLeft cut rhs pivot) ∧
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=rawPiece++
        [.inr (.inr (.inl (.inr false))),.inr (.inl ⟨.inr false,.inr ()⟩)] ∧
      ActionCanonicalBlocks site principal (Sum.inl pivot::rawPiece)
        (site.outsideEnd pivot::source.segments) ∧
      PlugLabelling cut rhs (Sum.inl pivot::rawPiece) seam output := by
  obtain ⟨pending,whole,_sourceLabels,_sourceEnd,trimmed⟩ :=
    site.bra_aux_canonical_access flow root positive sourceMatches principal source.access target.access
      (source.word.trans target.word.symm) false endAt labels
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨middle,assignment,_pieceLabels⟩ := target.assignments a b labels
  rw [targetCut.1] at assignment
  have parentLabels : Labelling site.reduce targetParent.val a middle := by
    rcases assignment with ⟨empty,_⟩ | actual
    · have head := targetParent.property.2.1;rw [empty] at head;cases head
    · exact actual
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  obtain ⟨parent,_parentLabels,parentFinish⟩ :=
    site.action_kept_canonical_access (.bra .app i j lt) flow root positive sourceMatches principal
      sourceParent targetParent parentWord parentNode parentPort parentEnd parentLabels
  let pivot : Endpoint cut := (cut).wire (.inl ⟨parentNode,parentPort⟩)
  have oldLast : sourceParent.val.getLast?=some (site.outsideEnd pivot) := by
    change sourceParent.val.getLast?=some (site.outsideEnd ((cut).wire (.inl ⟨parentNode,parentPort⟩)))
    rw [←site.outsideEnd_wire];exact parentFinish
  have newLast : targetParent.val.getLast?=some (AG.plugLeft cut rhs pivot) :=
    parentEnd.trans (congrArg some (plugLeft_wire cut rhs (.inl ⟨parentNode,parentPort⟩)))
  have rawLast : (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun).getLast?=
      some (Sum.inl pivot) := by
    rw [List.getLast?_map,newLast]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl pivot))
  obtain ⟨initial,parentShape⟩ := List.getLast?_eq_some_iff.mp rawLast
  have untrimmed : (initial++[Sum.inl pivot])++
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=pending.pre++
        [.inr (.inr (.inl (.inr false))),.inr (.inl ⟨.inr false,.inr ()⟩)] := by
    rw [←parentShape,←List.map_append,←targetCut.2]
    exact trimmed
  obtain ⟨rawPiece,prefixSplit,pieceSplit⟩ := trim_after_literal_pivot initial
    (target.segments.map (plugEnd (cut).label (rhs).label).invFun) pending.pre (Sum.inl pivot)
    (.inr (.inr (.inl (.inr false)))) (.inr (.inl ⟨.inr false,.inr ()⟩))
    untrimmed (by intro wrong;cases wrong) (by intro wrong;cases wrong)
  have rawSplit : pending.pre=
      targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++rawPiece := by
    rw [parentShape];exact prefixSplit
  obtain ⟨oldPiece,seam,oldSplit,relation,_sameParentLabels,pieceLabels⟩ :=
    whole.cut_at_raw_parent site parent pending.prefixPath.labelling rawSplit pivot rawLast
  have sourceCut := (source.child_prefix sourceMatches role sourceParent sourceWord).2
  have samePiece : oldPiece=source.segments := List.append_cancel_left (oldSplit.symm.trans sourceCut)
  rw [samePiece] at relation
  exact ⟨pivot,rawPiece,seam,pending.middle,oldLast,newLast,pieceSplit,relation,pieceLabels⟩
end
end Lamping.AG

#print axioms Lamping.AG.SourceEdgeFragment.cro_kept_parent_copied_app_context_cut
#print axioms Lamping.AG.SourceEdgeFragment.bra_kept_parent_copied_app_context_cut
