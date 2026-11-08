import Lamping.Lamping.ActionKeptParentCuts
import Lamping.Lamping.ActionCopiedBindingFragmentCuts
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "s" => Schema.croAction Op.lam i j lt
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed
private abbrev copiedLambdaCroRight (i j : Nat) (lt : i<j) := (Schema.croAction Op.lam i j lt).right.net
local notation "rhs" => copiedLambdaCroRight i j lt

/-- Fixed local body padding is built from the supplied actual lambda access.
The canonical cut fixes the actual parent ordinal and derives the OLD split. -/
theorem SourceEdgeFragment.cro_kept_parent_copied_lambda_cut
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
    (endAt : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    {a b : Context} (labels : Labelling site.reduce target.access.val a b) :
    ∃ pivot : Endpoint cut,∃ seam output : Context,
      sourceParent.val.getLast?=some (site.outsideEnd pivot) ∧
      targetParent.val.getLast?=some (AG.plugLeft cut rhs pivot) ∧
      ActionCanonicalBlocks site principal
        (Sum.inl pivot::(target.segments.map (plugEnd (cut).label (rhs).label).invFun++
          [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
            .inl (.inr (.inl (.inr (.inr true))))]))
        (site.outsideEnd pivot::(source.segments++[.inl ⟨.inr (.inr ()),.inr true⟩])) ∧
      PlugLabelling cut rhs
        (Sum.inl pivot::(target.segments.map (plugEnd (cut).label (rhs).label).invFun++
          [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
            .inl (.inr (.inl (.inr (.inr true))))])) seam output := by
  have sameWord := source.word.trans target.word.symm
  have whole := site.cro_lambda_canonical_access flow root positive sourceMatches principal
    source.access target.access sameWord endAt labels
  obtain ⟨_sourcePadding,_sourceFinish,paddedLabels⟩ :=
    site.cro_lambda_padding_labels flow root positive sourceMatches principal
      source.access target.access sameWord endAt labels
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
    site.action_kept_canonical_access (.cro .lam i j lt) flow root positive sourceMatches principal
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
  have rawSplit :
      target.access.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))]=
      targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
        (target.segments.map (plugEnd (cut).label (rhs).label).invFun++
          [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
            .inl (.inr (.inl (.inr (.inr true))))]) := by
    rw [targetCut.2,List.map_append,List.append_assoc]
  obtain ⟨oldPiece,seam,oldSplit,relation,_sameParentLabels,pieceLabels⟩ :=
    whole.cut_at_raw_parent site parent paddedLabels rawSplit pivot rawLast
  have sourceCut := (source.child_prefix sourceMatches role sourceParent sourceWord).2
  rw [sourceCut,List.append_assoc] at oldSplit
  have samePiece : oldPiece=source.segments++[.inl ⟨.inr (.inr ()),.inr true⟩] :=
    (List.append_cancel_left oldSplit).symm
  rw [samePiece] at relation
  exact ⟨pivot,seam,InitialOffsets.croAt i b,oldLast,newLast,relation,pieceLabels⟩
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "s" => Schema.braAction Op.lam i j lt
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed
private abbrev copiedLambdaBraRight (i j : Nat) (lt : i<j) := (Schema.braAction Op.lam i j lt).right.net
local notation "rhs" => copiedLambdaBraRight i j lt

/-- Fixed local body padding is built from the supplied actual lambda access.
The canonical cut fixes the actual parent ordinal and derives the OLD split. -/
theorem SourceEdgeFragment.bra_kept_parent_copied_lambda_cut
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
    (endAt : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    {a b : Context} (labels : Labelling site.reduce target.access.val a b) :
    ∃ pivot : Endpoint cut,∃ seam output : Context,
      sourceParent.val.getLast?=some (site.outsideEnd pivot) ∧
      targetParent.val.getLast?=some (AG.plugLeft cut rhs pivot) ∧
      ActionCanonicalBlocks site principal
        (Sum.inl pivot::(target.segments.map (plugEnd (cut).label (rhs).label).invFun++
          [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
            .inl (.inr (.inl (.inr (.inr true))))]))
        (site.outsideEnd pivot::(source.segments++[.inl ⟨.inr (.inr ()),.inr true⟩])) ∧
      PlugLabelling cut rhs
        (Sum.inl pivot::(target.segments.map (plugEnd (cut).label (rhs).label).invFun++
          [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
            .inl (.inr (.inl (.inr (.inr true))))])) seam output := by
  have sameWord := source.word.trans target.word.symm
  have whole := site.bra_lambda_canonical_access flow root positive sourceMatches principal
    source.access target.access sameWord endAt labels
  obtain ⟨_sourcePadding,_sourceFinish,paddedLabels⟩ :=
    site.bra_lambda_padding_labels flow root positive sourceMatches principal
      source.access target.access sameWord endAt labels
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
    site.action_kept_canonical_access (.bra .lam i j lt) flow root positive sourceMatches principal
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
  have rawSplit :
      target.access.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))]=
      targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
        (target.segments.map (plugEnd (cut).label (rhs).label).invFun++
          [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
            .inl (.inr (.inl (.inr (.inr true))))]) := by
    rw [targetCut.2,List.map_append,List.append_assoc]
  obtain ⟨oldPiece,seam,oldSplit,relation,_sameParentLabels,pieceLabels⟩ :=
    whole.cut_at_raw_parent site parent paddedLabels rawSplit pivot rawLast
  have sourceCut := (source.child_prefix sourceMatches role sourceParent sourceWord).2
  rw [sourceCut,List.append_assoc] at oldSplit
  have samePiece : oldPiece=source.segments++[.inl ⟨.inr (.inr ()),.inr true⟩] :=
    (List.append_cancel_left oldSplit).symm
  rw [samePiece] at relation
  exact ⟨pivot,seam,InitialOffsets.braAt i b,oldLast,newLast,relation,pieceLabels⟩
end
end Lamping.AG

