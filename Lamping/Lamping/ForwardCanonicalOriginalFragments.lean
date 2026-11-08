import Lamping.Lamping.ParentCanonicalFarComparison
import Lamping.Lamping.ForwardExpandedLastHistoryOrigins
import Lamping.Lamping.FamilyRepresentation

namespace Lamping.Lambda.Labelled
open SyntaxIncidence

/-- At one literal edge the actual incidence record is unique. -/
theorem IncomingIncidenceSnapshot.unique
    (left right : IncomingIncidenceSnapshot t edge) : left=right := by
  cases left with
  | mk lf lt lfrom lto =>
    cases right with
    | mk rf rt rfrom rto =>
      have fromEq:=Source.unique lfrom rfrom
      have toEq:=Target.unique lto rto
      cases fromEq
      cases toEq
      rfl
end Lamping.Lambda.Labelled

namespace Lamping.AG
open Graph Lambda Lambda.Labelled SyntaxIncidence
variable {source current : LTerm}

/-- Proof output aligned to THIS canonical FAR producer's snapshot. -/
structure CanonicalRecentLastOutput
    {F ps : List Path} {degree : Label} {start : Path} {edges : List Path}
    (labels : History ps source current)
    (cut : ActualUnsafeMarkerCut F ps source current degree start edges)
    (snapshot : IncomingIncidenceSnapshot current cut.edge)
    (canonical : CanonicalAfterFarOutput labels cut snapshot) where
  leaf : DirectedMarkerLeafOutput F source degree cut.forward ps
    (cut.node.label.readLetters cut.forward)
  geometry : SpineIncidenceProvenance F source degree cut.forward
    cut.spine cut.lookup leaf snapshot
  recent : RecentSpineFrame geometry
  compatibility : RecentFarCompatibility canonical recent
  low : ExpandedLastSelectedEndpoint recent.packet.middle recent.packet.site
    (recent.packet.frame.edges.getLastD []) cut.forward (some compatibility.expandedProper)
  original : ExpandedLastOriginalEndpoints F source recent.packet.middle degree
    recent.packet.event.labels (recent.packet.frame.edges.getLastD []) low.node
    cut.forward canonical.sourceProper compatibility.originalEdges

theorem canonical_recent_last_output
    {labels : History ps source current}
    {cut : ActualUnsafeMarkerCut F ps source current degree start edges}
    {snapshot : IncomingIncidenceSnapshot current cut.edge}
    (canonical : CanonicalAfterFarOutput labels cut snapshot)
    (closed : Closed source.erase)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree)) :
    Nonempty (CanonicalRecentLastOutput labels cut snapshot canonical) := by
  obtain ⟨leaf,other,⟨geometry⟩⟩:=cut.spine.incidence_leaf_output closed cut.lookup
  have snapshotEq:=other.unique snapshot
  have actual : SpineIncidenceProvenance F source degree cut.forward
      cut.spine cut.lookup leaf snapshot := snapshotEq ▸ geometry
  obtain ⟨recent⟩:=actual.recent_frame
  obtain ⟨compatibility⟩:=Lamping.AG.RecentSpineFrame.canonical_far_compatibility recent canonical
  obtain ⟨low,⟨original⟩⟩:=compatibility.expanded_last_endpoints selected sourceSafe
  exact ⟨⟨leaf,actual,recent,compatibility,low,original⟩⟩

section
variable {F ps : List Path} {degree : Label}
variable {labels : History ps source current}
variable {leftCut : ActualUnsafeMarkerCut F ps source current degree leftStart leftEdges}
variable {rightCut : ActualUnsafeMarkerCut F ps source current degree rightStart rightEdges}
variable {leftSnapshot : IncomingIncidenceSnapshot current leftCut.edge}
variable {rightSnapshot : IncomingIncidenceSnapshot current rightCut.edge}
variable (closed : Closed source.erase)
variable (left : CanonicalAfterFarOutput labels leftCut leftSnapshot)
variable (right : CanonicalAfterFarOutput labels rightCut rightSnapshot)

/-- Derived facts about two actual original LAST edges, not a graph premise. -/
structure ForwardCanonicalOriginalComparison where
  leftOutput : CanonicalRecentLastOutput labels leftCut leftSnapshot left
  rightOutput : CanonicalRecentLastOutput labels rightCut rightSnapshot right
  labelEq : leftOutput.original.original.label=rightOutput.original.original.label
  leftAux : AuxiliaryAt source leftOutput.original.oldEdge
  rightAux : AuxiliaryAt source rightOutput.original.oldEdge
  sourceIso : SuccessfulEndpointIso source closed
    (some leftOutput.original.fromVertex) (some rightOutput.original.fromVertex)
  targetIso : SuccessfulEndpointIso source closed
    (some leftOutput.original.toVertex) (some rightOutput.original.toVertex)
end

private theorem bool_recent_source_comparison
    {F ps : List Path} {degree : Label} {leftDirection rightDirection : Bool}
    {leftNode rightNode : LTerm} {leftBefore rightBefore : List (Option Label)}
    {leftEdge rightEdge : Path}
    {leftSpine : DirectedMarkerSpine F source degree leftDirection ps current leftBefore leftEdge}
    {rightSpine : DirectedMarkerSpine F source degree rightDirection ps current rightBefore rightEdge}
    {leftLookup : current.subterm leftEdge=some leftNode}
    {rightLookup : current.subterm rightEdge=some rightNode}
    {leftLeaf : DirectedMarkerLeafOutput F source degree leftDirection ps (leftNode.label.readLetters leftDirection)}
    {rightLeaf : DirectedMarkerLeafOutput F source degree rightDirection ps (rightNode.label.readLetters rightDirection)}
    {leftSnapshot : IncomingIncidenceSnapshot current leftEdge}
    {rightSnapshot : IncomingIncidenceSnapshot current rightEdge}
    {leftGeometry : SpineIncidenceProvenance F source degree leftDirection leftSpine leftLookup leftLeaf leftSnapshot}
    {rightGeometry : SpineIncidenceProvenance F source degree rightDirection rightSpine rightLookup rightLeaf rightSnapshot}
    (left : RecentSpineFrame leftGeometry) (right : RecentSpineFrame rightGeometry)
    (labels : History ps source current)
    {leftLast rightLast : LTerm} {leftFar rightFar : ProperPosition source}
    {leftFarEdges rightFarEdges : List Path}
    (leftOut : ExpandedLastOriginalEndpoints F source left.packet.middle degree left.packet.event.labels
      (left.packet.frame.edges.getLastD []) leftLast leftDirection leftFar leftFarEdges)
    (rightOut : ExpandedLastOriginalEndpoints F source right.packet.middle degree right.packet.event.labels
      (right.packet.frame.edges.getLastD []) rightLast rightDirection rightFar rightFarEdges)
    {marked : Marked}
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) marked)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (closed : Closed source.erase)
    (leftMarked : ¬leftNode.label.OuterBarsSafe (fun x=>x≠degree))
    (rightMarked : ¬rightNode.label.OuterBarsSafe (fun x=>x≠degree))
    (same : leftNode.label=rightNode.label)
    (leftTrue : leftDirection=true) (rightTrue : rightDirection=true) :
    leftOut.original.label=rightOut.original.label ∧
      SuccessfulEndpointIso source closed (some leftOut.fromVertex) (some rightOut.fromVertex) := by
  subst leftDirection
  subst rightDirection
  exact recent_forward_expanded_last_source_comparison left right labels leftOut rightOut old
    selected sourceSafe closed leftMarked rightMarked same

theorem canonical_forward_original_comparison
    {F ps : List Path} {degree : Label} {marked : Marked}
    (labels : History ps source current)
    (closed : Closed source.erase)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) marked)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (leftCut : ActualUnsafeMarkerCut F ps source current degree leftStart leftEdges)
    (rightCut : ActualUnsafeMarkerCut F ps source current degree rightStart rightEdges)
    (leftMore : leftCut.after≠[]) (rightMore : rightCut.after≠[])
    (leftTrue : leftCut.forward=true) (rightTrue : rightCut.forward=true)
    (sameHead : leftCut.node.label=rightCut.node.label)
    {leftSnapshot : IncomingIncidenceSnapshot current leftCut.edge}
    {rightSnapshot : IncomingIncidenceSnapshot current rightCut.edge}
    (left : CanonicalAfterFarOutput labels leftCut leftSnapshot)
    (right : CanonicalAfterFarOutput labels rightCut rightSnapshot)
    (good : CanonicalFarFullComparison closed left right) :
    Nonempty (ForwardCanonicalOriginalComparison closed left right) := by
  obtain ⟨lo⟩:=canonical_recent_last_output left closed selected sourceSafe
  obtain ⟨ro⟩:=canonical_recent_last_output right closed selected sourceSafe
  obtain ⟨labelEq,sourceIso⟩:=bool_recent_source_comparison lo.recent ro.recent labels lo.original ro.original
    old selected sourceSafe closed leftCut.marked rightCut.marked sameHead leftTrue rightTrue
  have leftAux:=leftCut.forward_original_last_auxiliary leftTrue leftMore lo.recent lo.original
  have rightAux:=rightCut.forward_original_last_auxiliary rightTrue rightMore ro.recent ro.original
  have leftTarget : lo.original.toVertex=left.sourceProper ∧lo.original.targetEdges=lo.compatibility.originalEdges := by
    simpa only [leftTrue,if_true] using lo.original.targetClass
  have rightTarget : ro.original.toVertex=right.sourceProper ∧ro.original.targetEdges=ro.compatibility.originalEdges := by
    simpa only [rightTrue,if_true] using ro.original.targetClass
  have targetIso : SuccessfulEndpointIso source closed (some lo.original.toVertex) (some ro.original.toVertex) := by
    refine ⟨lo.original.targetEdges,ro.original.targetEdges,lo.original.targetChain,ro.original.targetChain,?_⟩
    rw [leftTarget.2,rightTarget.2,lo.compatibility.exactSourceEdges,ro.compatibility.exactSourceEdges]
    exact good.2
  exact ⟨⟨lo,ro,labelEq,leftAux,rightAux,sourceIso,targetIso⟩⟩

private theorem nonterminal_not_redex
    (chain : PrerequisiteChain t start (edge::after))
    (more : after≠[]) : ¬PrerequisiteRedexEdge t edge := by
  obtain ⟨before,last,split,_redex,earlier⟩:=chain.redex_only_last
  cases before with
  | nil =>
    simp only [List.nil_append,List.cons.injEq] at split
    exact False.elim (more split.2)
  | cons head tail =>
    have same : edge=head:=(List.cons.inj split).1
    exact earlier edge (by rw [same];exact List.mem_cons_self)

/-- Choose the natural B2 cuts ONCE. Only its nonterminal TRUE branch is
extended; all-safe, terminal and other directions retain their honest scope. -/
theorem actual_parent_canonical_forward_original_comparison
    {initialSource source current : LTerm} {prior ps F : List Path} {degree : Label} {n : Marked}
    (initial : INIT initialSource) (prefixHistory : History prior initialSource source)
    (sourceClosed : Closed source.erase)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) n)
    (labels : History ps source current)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (leftChain : PrerequisiteChain current leftStart leftEdges)
    (rightChain : PrerequisiteChain current rightStart rightEdges)
    (wholeIso : ChainIncidenceIso
      (chainSyntaxIncidence current (labels.closed sourceClosed) leftEdges)
      (chainSyntaxIncidence current (labels.closed sourceClosed) rightEdges)) :
    ((∀e∈leftEdges,degreeReadSafe degree (current.labelAt e)) ∧
     (∀e∈rightEdges,degreeReadSafe degree (current.labelAt e))) ∨
    ∃leftCut : ActualUnsafeMarkerCut F ps source current degree leftStart leftEdges,
      ∃rightCut : ActualUnsafeMarkerCut F ps source current degree rightStart rightEdges,
        leftCut.before.length=rightCut.before.length ∧
        leftCut.before.map current.labelAt=rightCut.before.map current.labelAt ∧
        current.labelAt leftCut.edge=current.labelAt rightCut.edge ∧
        leftCut.after.map current.labelAt=rightCut.after.map current.labelAt ∧
        ((leftCut.after=[] ∧rightCut.after=[]) ∨
         (leftCut.after≠[] ∧rightCut.after≠[] ∧
          ∃leftSnapshot rightSnapshot,
            ∃left : CanonicalAfterFarOutput labels leftCut leftSnapshot,
              ∃right : CanonicalAfterFarOutput labels rightCut rightSnapshot,
                CanonicalFarFullComparison sourceClosed left right ∧
                (leftCut.forward=true →Nonempty (ForwardCanonicalOriginalComparison sourceClosed left right)))) := by
  rcases actual_parent_cuts_canonical_far_comparison initial prefixHistory sourceClosed old labels
    selected sourceSafe leftChain rightChain wholeIso with safe | cuts
  · exact Or.inl safe
  · obtain ⟨lc,rc,len,front,head,back,emptyOr⟩:=cuts
    refine Or.inr ⟨lc,rc,len,front,head,back,?_⟩
    rcases emptyOr with empty | more
    · exact Or.inl empty
    · obtain ⟨lm,rm,ls,rs,left,right,good⟩:=more
      refine Or.inr ⟨lm,rm,ls,rs,left,right,good,?_⟩
      intro positive
      have headEq : lc.node.label=rc.node.label := by
        simpa only [LTerm.labelAt,lc.lookup,rc.lookup,Option.map_some,Option.some.injEq] using head
      have direction:=(prefixHistory.append labels).equal_label_nonredex_read_direction initial
        lc.lookup rc.lookup headEq lc.reading rc.reading
        (nonterminal_not_redex lc.remaining lm) (nonterminal_not_redex rc.remaining rm)
      have rightTrue : rc.forward=true := direction.symm.trans positive
      exact canonical_forward_original_comparison labels sourceClosed old selected sourceSafe lc rc
        lm rm positive rightTrue headEq left right good

def CanonicalRecentLastOutput.originalEdge
    {labels : History ps source current}
    {cut : ActualUnsafeMarkerCut F ps source current degree start edges}
    {snapshot : IncomingIncidenceSnapshot current cut.edge}
    {canonical : CanonicalAfterFarOutput labels cut snapshot}
    (out : CanonicalRecentLastOutput labels cut snapshot canonical) : Edge source :=
  ⟨out.original.oldEdge,by rw [←LTerm.erase_subterm,out.original.lookup];rfl⟩

/-- Literal original SOURCE pieces follow from the genuine SOURCE Aux IH;
no marked local LAST evaluator or current REP conclusion is supplied. -/
theorem ForwardCanonicalOriginalComparison.source_fragments
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    {labels : History ps source current}
    {leftCut : ActualUnsafeMarkerCut F ps source current degree leftStart leftEdges}
    {rightCut : ActualUnsafeMarkerCut F ps source current degree rightStart rightEdges}
    {leftSnapshot : IncomingIncidenceSnapshot current leftCut.edge}
    {rightSnapshot : IncomingIncidenceSnapshot current rightCut.edge}
    {left : CanonicalAfterFarOutput labels leftCut leftSnapshot}
    {right : CanonicalAfterFarOutput labels rightCut rightSnapshot}
    {closed : Closed source.erase}
    (comparison : ForwardCanonicalOriginalComparison closed left right)
    (selection : OccurrenceFragmentSelection source g root)
    (auxiliary : AuxiliarySeparation closed selection) :
    (selection comparison.leftOutput.originalEdge).fragment.segments=
      (selection comparison.rightOutput.originalEdge).fragment.segments := by
  classical
  apply Classical.byContradiction
  intro different
  have labelEq : SyntaxIncidence.label source comparison.leftOutput.originalEdge=
      SyntaxIncidence.label source comparison.rightOutput.originalEdge := by
    rw [SyntaxIncidence.label_of_lookup source _ comparison.leftOutput.original.lookup,
      SyntaxIncidence.label_of_lookup source _ comparison.rightOutput.original.lookup]
    exact comparison.labelEq
  apply auxiliary comparison.leftOutput.originalEdge comparison.rightOutput.originalEdge
    comparison.leftAux comparison.rightAux labelEq different
  constructor
  · rw [SyntaxIncidence.source_eq_of_spec source _ comparison.leftOutput.original.sourceSpec,
      SyntaxIncidence.source_eq_of_spec source _ comparison.rightOutput.original.sourceSpec]
    exact comparison.sourceIso
  · rw [SyntaxIncidence.target_eq_of_spec source closed _ comparison.leftOutput.original.targetSpec,
      SyntaxIncidence.target_eq_of_spec source closed _ comparison.rightOutput.original.targetSpec]
    exact comparison.targetIso

#print axioms IncomingIncidenceSnapshot.unique
#print axioms canonical_recent_last_output
#print axioms canonical_forward_original_comparison
#print axioms actual_parent_canonical_forward_original_comparison
#print axioms ForwardCanonicalOriginalComparison.source_fragments
end Lamping.AG
