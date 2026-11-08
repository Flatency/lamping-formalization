import Lamping.Lamping.ActionCopiedBindingFragmentCuts
import Lamping.Lamping.ActionKeptFragmentComparison
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.croAction Op.lam i j lt) V) site.closed
private abbrev croBodyKeptRight (i j : Nat) (lt : i<j) := (Schema.croAction .lam i j lt).right.net
local notation "rhs" => croBodyKeptRight i j lt
 theorem SourceEdgeFragment.cro_copied_lambda_body_kept_cut
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
    (parentFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (node : K) (port : Port (kept node).sort)
    (endAt : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl node,port⟩)))
    {a b : Context} (wholeLabels : Labelling site.reduce target.access.val a b) :
    ∃tail oldTail seam,
      source.segments=.inl ⟨.inr (.inr ()),.inr true⟩::oldTail ∧
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=
        .inr (.inl ⟨.inl (),.inr true⟩)::.inr (.inl ⟨.inr true,.inl ()⟩)::
          .inl (.inr (.inl (.inr (.inr true))))::tail ∧
      ActionCanonicalBlocks site principal (.inl (.inr (.inl (.inr (.inr true))))::tail) source.segments ∧
      PlugLabelling cut rhs (.inl (.inr (.inl (.inr (.inr true))))::tail) seam b := by
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨middle,assignment,pieceLabels⟩ := target.assignments a b wholeLabels
  rw [targetCut.1] at assignment
  have parentLabels : Labelling site.reduce targetParent.val a middle := by
    rcases assignment with ⟨empty,_⟩|labels
    · have head:=targetParent.property.2.1;rw [empty] at head;cases head
    · exact labels
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val := by
    have same := sourceWord.symm.trans targetWord
    exact List.append_cancel_right same
  obtain ⟨padLabels,sourceFinish,paddedLabels⟩ := site.cro_lambda_padding_labels flow root positive sourceMatches
    principal sourceParent targetParent parentWord parentFinish parentLabels
  have parentRelation := site.cro_lambda_canonical_access flow root positive sourceMatches principal
    sourceParent targetParent parentWord parentFinish parentLabels
  have fromEndpoint := actual_lambda_child_head sourceMatches source role sourceParent sourceWord
    (.inr (.inr ())) (.inl ()) (.inr true) HEq.rfl sourceFinish
  have sourceHead := source.start
  rw [fromEndpoint] at sourceHead
  obtain ⟨oldTail,sourcePiece⟩ := List.head?_eq_some_iff.mp sourceHead
  obtain ⟨fullTail,writerMiddle,targetPiece,writer,suffix⟩ := unary_copied_lambda_body_fragment cut .cro
    (Bij.refl Unit) (Or.inl rfl) i (j-1) (current:=current) targetMatches target role targetParent targetWord parentFinish pieceLabels
  change List (PlugSegment cut rhs) at fullTail
  change target.segments.map (plugEnd (cut).label (rhs).label).invFun=
    .inr (.inl ⟨.inl (),.inr true⟩)::.inr (.inl ⟨.inr true,.inl ()⟩)::
      .inl (.inr (.inl (.inr (.inr true))))::fullTail at targetPiece
  obtain ⟨whole,_,_⟩ := site.action_kept_canonical_access (.cro .lam i j lt) flow root positive sourceMatches principal
    source.access target.access (source.word.trans target.word.symm) node port endAt wholeLabels
  let tail := fullTail
  have sourceCut := source.child_prefix sourceMatches role sourceParent sourceWord
  have oldSplit : source.access.val=(sourceParent.val++[.inl ⟨.inr (.inr ()),.inr true⟩])++oldTail := by
    rw [sourceCut.2,sourcePiece]
    simp only [List.append_assoc,List.singleton_append]
  have rawSplit : target.access.val.map (plugEnd (cut).label (rhs).label).invFun=
      (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))])++tail := by
    rw [targetCut.2,List.map_append,targetPiece]
    simp only [tail,List.append_assoc,List.cons_append,List.nil_append]
  have parentLast : (sourceParent.val++[.inl ⟨.inr (.inr ()),.inr true⟩] : List (Endpoint site.net)).getLast?=
      some (site.outsideEnd (.inr (.inl (.inr (.inr true))))) := by
    simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
    rfl
  obtain ⟨seam,relation,actualLabels⟩ := whole.unary_cut_at_actual_prefix site (by intro h;cases h)
    parentRelation (wholeLabels.plug_decomposition cut rhs) paddedLabels oldSplit rawSplit
    (.inr (.inl (.inr (.inr true)))) parentLast
  refine ⟨tail,oldTail,seam,sourcePiece,targetPiece,?_,actualLabels⟩
  · simpa only [sourcePiece] using relation
end
end Lamping.AG
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.braAction Op.lam i j lt) V) site.closed
private abbrev braBodyKeptRight (i j : Nat) (lt : i<j) := (Schema.braAction .lam i j lt).right.net
local notation "rhs" => braBodyKeptRight i j lt
 theorem SourceEdgeFragment.bra_copied_lambda_body_kept_cut
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
    (parentFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (node : K) (port : Port (kept node).sort)
    (endAt : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl node,port⟩)))
    {a b : Context} (wholeLabels : Labelling site.reduce target.access.val a b) :
    ∃tail oldTail seam,
      source.segments=.inl ⟨.inr (.inr ()),.inr true⟩::oldTail ∧
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=
        .inr (.inl ⟨.inl (),.inr true⟩)::.inr (.inl ⟨.inr true,.inl ()⟩)::
          .inl (.inr (.inl (.inr (.inr true))))::tail ∧
      ActionCanonicalBlocks site principal (.inl (.inr (.inl (.inr (.inr true))))::tail) source.segments ∧
      PlugLabelling cut rhs (.inl (.inr (.inl (.inr (.inr true))))::tail) seam b := by
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨middle,assignment,pieceLabels⟩ := target.assignments a b wholeLabels
  rw [targetCut.1] at assignment
  have parentLabels : Labelling site.reduce targetParent.val a middle := by
    rcases assignment with ⟨empty,_⟩|labels
    · have head:=targetParent.property.2.1;rw [empty] at head;cases head
    · exact labels
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val := by
    have same := sourceWord.symm.trans targetWord
    exact List.append_cancel_right same
  obtain ⟨padLabels,sourceFinish,paddedLabels⟩ := site.bra_lambda_padding_labels flow root positive sourceMatches
    principal sourceParent targetParent parentWord parentFinish parentLabels
  have parentRelation := site.bra_lambda_canonical_access flow root positive sourceMatches principal
    sourceParent targetParent parentWord parentFinish parentLabels
  have fromEndpoint := actual_lambda_child_head sourceMatches source role sourceParent sourceWord
    (.inr (.inr ())) (.inl ()) (.inr true) HEq.rfl sourceFinish
  have sourceHead := source.start
  rw [fromEndpoint] at sourceHead
  obtain ⟨oldTail,sourcePiece⟩ := List.head?_eq_some_iff.mp sourceHead
  obtain ⟨fullTail,writerMiddle,targetPiece,writer,suffix⟩ := unary_copied_lambda_body_fragment cut .bra
    (Bij.refl Unit) (Or.inr rfl) i (j+1) (current:=current) targetMatches target role targetParent targetWord parentFinish pieceLabels
  change List (PlugSegment cut rhs) at fullTail
  change target.segments.map (plugEnd (cut).label (rhs).label).invFun=
    .inr (.inl ⟨.inl (),.inr true⟩)::.inr (.inl ⟨.inr true,.inl ()⟩)::
      .inl (.inr (.inl (.inr (.inr true))))::fullTail at targetPiece
  obtain ⟨whole,_,_⟩ := site.action_kept_canonical_access (.bra .lam i j lt) flow root positive sourceMatches principal
    source.access target.access (source.word.trans target.word.symm) node port endAt wholeLabels
  let tail := fullTail
  have sourceCut := source.child_prefix sourceMatches role sourceParent sourceWord
  have oldSplit : source.access.val=(sourceParent.val++[.inl ⟨.inr (.inr ()),.inr true⟩])++oldTail := by
    rw [sourceCut.2,sourcePiece]
    simp only [List.append_assoc,List.singleton_append]
  have rawSplit : target.access.val.map (plugEnd (cut).label (rhs).label).invFun=
      (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))])++tail := by
    rw [targetCut.2,List.map_append,targetPiece]
    simp only [tail,List.append_assoc,List.cons_append,List.nil_append]
  have parentLast : (sourceParent.val++[.inl ⟨.inr (.inr ()),.inr true⟩] : List (Endpoint site.net)).getLast?=
      some (site.outsideEnd (.inr (.inl (.inr (.inr true))))) := by
    simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
    rfl
  obtain ⟨seam,relation,actualLabels⟩ := whole.unary_cut_at_actual_prefix site (by intro h;cases h)
    parentRelation (wholeLabels.plug_decomposition cut rhs) paddedLabels oldSplit rawSplit
    (.inr (.inl (.inr (.inr true)))) parentLast
  refine ⟨tail,oldTail,seam,sourcePiece,targetPiece,?_,actualLabels⟩
  · simpa only [sourcePiece] using relation
end
end Lamping.AG