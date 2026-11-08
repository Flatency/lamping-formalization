import Lamping.Lamping.FanCopiedLambdaBodyPrefixes
import Lamping.Lamping.ActionRawOutsideCut
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.lam i j lt) V) site.closed
private abbrev bodyKeptRight (i j : Nat) (lt : i<j) := (Schema.fanAction Op.lam i j lt).right.net
local notation "rhs" => bodyKeptRight i j lt
local notation "writer2" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "pivot" => (Sum.inr (Sum.inl (Sum.inr (Sum.inr true))) : Endpoint cut)
local notation "oldBody" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) (Sum.inr true)) : Endpoint site.net)
/-- Actual copied BODY parent and kept terminal: parent normalization is a
literal prefix of THIS child whole, and its OLD suffix is THIS sourcepiece. -/
theorem SourceEdgeFragment.fan_copied_body_kept_cut
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm .body edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[.body])
    (targetWord : position=accessWord site.reduce targetParent.val++[.body])
    (parentBranch : Bool)
    (parentFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl parentBranch),.inl ()⟩)))
    (terminal : K) (port : Port (kept terminal).sort)
    (childFinish : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl terminal,port⟩)))
    {a b : Context} (labels : Labelling site.reduce target.access.val a b) :
    ∃ (tail : List (PlugSegment cut rhs)) (oldTail : List (Endpoint site.net)) (seam : Context),
      source.segments=oldBody::oldTail ∧
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=
        Sum.inr (Sum.inl ⟨Sum.inl parentBranch,Sum.inr true⟩)::writer2::Sum.inl pivot::tail ∧
      ActionCanonicalBlocks site principal (Sum.inl pivot::tail) source.segments ∧
      PlugLabelling cut rhs (Sum.inl pivot::tail) seam b := by
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨middle,assignment,pieceLabels⟩ := target.assignments a b labels
  rw [targetCut.1] at assignment
  have parentLabels : Labelling site.reduce targetParent.val a middle := by
    rcases assignment with ⟨empty,_⟩|actual
    · have head:=targetParent.property.2.1;rw [empty] at head;cases head
    · exact actual
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  obtain ⟨parent,_parentLabels⟩ := site.fan_lambda_body_parent_canonical flow root positive
    sourceMatches principal sourceParent targetParent parentWord parentBranch parentFinish parentLabels
  obtain ⟨whole,_oldLabels,_oldFinish⟩ := site.action_kept_canonical_access (.fan .lam i j lt)
    flow root positive sourceMatches principal source.access target.access (source.word.trans target.word.symm)
    terminal port childFinish labels
  obtain ⟨tail,_writerMiddle,shape,_writerRule,_tailLabels⟩ := fan_copied_lambda_body_fragment
    cut i j parentBranch targetMatches target role targetParent targetWord parentFinish pieceLabels
  change List (PlugSegment cut rhs) at tail
  change target.segments.map (plugEnd (cut).label (rhs).label).invFun=
    Sum.inr (Sum.inl ⟨Sum.inl parentBranch,Sum.inr true⟩)::writer2::Sum.inl pivot::tail at shape
  let paddedParent := targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
    [Sum.inr (Sum.inl ⟨Sum.inl parentBranch,Sum.inr true⟩),writer2,Sum.inl pivot]
  have rawSplit : target.access.val.map (plugEnd (cut).label (rhs).label).invFun=paddedParent++tail := by
    rw [targetCut.2,List.map_append,shape]
    simp only [paddedParent,List.append_assoc,List.cons_append,List.nil_append]
  have parentLast : paddedParent.getLast?=some (Sum.inl pivot) := by
    simp only [paddedParent,List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨oldTail,seam,oldSplit,relation,_actualParentLabels,newLabels⟩ :=
    whole.cut_at_raw_parent site parent (labels.plug_decomposition cut rhs) rawSplit pivot parentLast
  have sourceCut := (source.child_prefix sourceMatches role sourceParent sourceWord).2
  have sourcePiece : source.segments=oldBody::oldTail := by
    apply List.append_cancel_left (as:=sourceParent.val)
    rw [←sourceCut]
    simpa only [List.append_assoc,List.singleton_append] using oldSplit
  change ActionCanonicalBlocks site principal (Sum.inl pivot::tail) (oldBody::oldTail) at relation
  rw [←sourcePiece] at relation
  exact ⟨tail,oldTail,seam,sourcePiece,shape,relation,newLabels⟩
end
end Lamping.AG
#print axioms Lamping.AG.SourceEdgeFragment.fan_copied_body_kept_cut
