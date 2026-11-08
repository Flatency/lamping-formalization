import Lamping.Lamping.ActualSpineAfterAlignment
import Lamping.Lamping.PairedCurrentChainSourceLabels
import Lamping.Lambda.ActualNodeLabelAncestry

namespace Lamping.AG
open Graph Lambda Lambda.Labelled SyntaxIncidence
variable {source current initialSource : LTerm}

/-- Canonical CURRENT proper FAR and its OWN actual original-source node.
The literal next occurrence, its binder target, and earliest triple LAST
are never identified by this output. -/
structure CanonicalAfterFarOutput
    {F ps : List Path} {degree : Label} {start : Path} {edges : List Path}
    (labels : History ps source current)
    (cut : ActualUnsafeMarkerCut F ps source current degree start edges)
    (snapshot : IncomingIncidenceSnapshot current cut.edge) where
  currentProper : ProperPosition current
  farEq : snapshot.far cut.forward=some currentProper
  literalNext : Path
  afterStart : ActualAfterStart current cut.reader cut.edge literalNext
  nextTarget : Target current literalNext (some currentProper)
  currentNode : LTerm
  currentLookup : current.subterm currentProper.val=some currentNode
  currentChain : PrerequisiteChain current currentProper.val cut.after
  exactEndpointChain : EndpointChain current (snapshot.far cut.forward) cut.after
  length_lt : cut.after.length<edges.length
  sourceProper : ProperPosition source
  sourceNode : LTerm
  sourceLookup : source.subterm sourceProper.val=some sourceNode
  constructorEq : sourceNode.constructorTag=currentNode.constructorTag
  nodeTrace : BetaNodeHistoryPreimage labels currentProper.val sourceProper.val
  vertexTrace : BetaVertexHistoryPreimage labels (some currentProper) (some sourceProper)
  sourceEdges : List Path
  sourceChain : PrerequisiteChain source sourceProper.val sourceEdges

/-- Actual endpoint chain inversion and existing operational node ancestry
construct every old coordinate and complete chain internally. -/
theorem ActualUnsafeMarkerCut.canonical_far_output
    (labels : History ps source current) (_sourceClosed : Closed source.erase)
    (cut : ActualUnsafeMarkerCut F ps source current degree start edges)
    (more : cut.after≠[]) (snapshot : IncomingIncidenceSnapshot current cut.edge) :
    Nonempty (CanonicalAfterFarOutput labels cut snapshot) := by
  classical
  obtain ⟨next,afterStart,nextTarget,endpointChain,length⟩ := cut.align_after_snapshot more snapshot
  cases farEq : snapshot.far cut.forward with
  | none =>
    simp only [farEq,EndpointChain] at endpointChain
  | some currentProper =>
    have chain : PrerequisiteChain current currentProper.val cut.after := by
      simpa only [farEq,EndpointChain] using endpointChain
    obtain ⟨node,lookup,notVariable⟩ : ∃node,current.subterm currentProper.val=some node ∧node.constructorTag≠0 := by
      rcases currentProper.property with ⟨stamp,fn,arg,lookup⟩ | ⟨stamp,body,lookup⟩
      · exact ⟨_,lookup,by simp [LTerm.constructorTag]⟩
      · exact ⟨_,lookup,by simp [LTerm.constructorTag]⟩
    obtain ⟨oldPosition,old,oldLookup,trace⟩ := labels.node_preimage_from_lookup lookup
    obtain ⟨sameOld,sameLookup,_last,tag⟩ := trace.lastAtom_constructor lookup
    have equal := Option.some.inj (sameLookup.symm.trans oldLookup)
    subst sameOld
    have proper : ProperAt source oldPosition := by
      cases old with
      | var stamp index => exact False.elim (notVariable tag.symm)
      | lam stamp body => exact Or.inr ⟨stamp,body,oldLookup⟩
      | app stamp fn arg => exact Or.inl ⟨stamp,fn,arg,oldLookup⟩
    let oldProper : ProperPosition source := ⟨oldPosition,proper⟩
    have actualOld : ∃oldEdges,PrerequisiteChain source oldPosition oldEdges := by
      apply Classical.byContradiction
      intro absent
      exact (trace.no_prerequisite absent) ⟨cut.after,chain⟩
    obtain ⟨oldEdges,oldChain⟩ := actualOld
    exact ⟨{
      currentProper:=currentProper,farEq:=farEq,literalNext:=next,afterStart:=afterStart
      nextTarget:=by simpa only [farEq] using nextTarget
      currentNode:=node,currentLookup:=lookup,currentChain:=chain,exactEndpointChain:=endpointChain,length_lt:=length
      sourceProper:=oldProper,sourceNode:=old,sourceLookup:=oldLookup,constructorEq:=tag,nodeTrace:=trace
      vertexTrace:=.proper trace,sourceEdges:=oldEdges,sourceChain:=oldChain }⟩

/-- Only an already actual SAME-history vertex trace can be compared to
this canonical ancestry; created SOURCE incidence is not a general hom. -/
theorem CanonicalAfterFarOutput.vertex_unique
    {labels : History ps source current}
    {cut : ActualUnsafeMarkerCut F ps source current degree start edges}
    {snapshot : IncomingIncidenceSnapshot current cut.edge}
    (output : CanonicalAfterFarOutput labels cut snapshot)
    (actual : BetaVertexHistoryPreimage labels (some output.currentProper) oldVertex) :
    oldVertex=some output.sourceProper := actual.unique output.vertexTrace

/-- Both good branches compare the EXACT producer-returned complete lists. -/
def CanonicalFarFullComparison
    {labels : History ps source current}
    {leftCut : ActualUnsafeMarkerCut F ps source current degree ls les}
    {rightCut : ActualUnsafeMarkerCut F ps source current degree rs res}
    {leftSnapshot : IncomingIncidenceSnapshot current leftCut.edge}
    {rightSnapshot : IncomingIncidenceSnapshot current rightCut.edge}
    (closed : Closed source.erase)
    (left : CanonicalAfterFarOutput labels leftCut leftSnapshot)
    (right : CanonicalAfterFarOutput labels rightCut rightSnapshot) : Prop :=
  left.sourceEdges.map source.labelAt=right.sourceEdges.map source.labelAt ∧
    ChainIncidenceIsomorphic (chainSyntaxIncidence source closed left.sourceEdges)
      (chainSyntaxIncidence source closed right.sourceEdges)

/-- The tail's OWN terminal/opposite-sign exception is retained. The
parent cuts having nonempty AFTER does not discharge this exception. -/
theorem canonical_after_far_comparison
    (initial : INIT initialSource) (prefixHistory : History prior initialSource source)
    (sourceClosed : Closed source.erase)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) n)
    (labels : History ps source current)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (leftCut : ActualUnsafeMarkerCut F ps source current degree ls les)
    (rightCut : ActualUnsafeMarkerCut F ps source current degree rs res)
    (leftMore : leftCut.after≠[]) (rightMore : rightCut.after≠[])
    (leftSnapshot : IncomingIncidenceSnapshot current leftCut.edge)
    (rightSnapshot : IncomingIncidenceSnapshot current rightCut.edge)
    (iso : ChainIncidenceIso
      (chainSyntaxIncidence current (labels.closed sourceClosed) leftCut.after)
      (chainSyntaxIncidence current (labels.closed sourceClosed) rightCut.after)) :
    ∃left : CanonicalAfterFarOutput labels leftCut leftSnapshot,
      ∃right : CanonicalAfterFarOutput labels rightCut rightSnapshot,
        (((∀e∈leftCut.after,degreeReadSafe degree (current.labelAt e)) ∧
          (∀e∈rightCut.after,degreeReadSafe degree (current.labelAt e))) ∧
          CanonicalFarFullComparison sourceClosed left right) ∨
        (∃lc : ActualUnsafeMarkerCut F ps source current degree left.currentProper.val leftCut.after,
          ∃rc : ActualUnsafeMarkerCut F ps source current degree right.currentProper.val rightCut.after,
            lc.forward=rc.forward ∧lc.before.map current.labelAt=rc.before.map current.labelAt ∧
            current.labelAt lc.edge=current.labelAt rc.edge ∧CanonicalFarFullComparison sourceClosed left right) ∨
        (∃lc : ActualUnsafeMarkerCut F ps source current degree left.currentProper.val leftCut.after,
          ∃rc : ActualUnsafeMarkerCut F ps source current degree right.currentProper.val rightCut.after,
            lc.after=[] ∧rc.after=[] ∧lc.forward≠rc.forward ∧
            lc.before.map current.labelAt=rc.before.map current.labelAt ∧current.labelAt lc.edge=current.labelAt rc.edge) := by
  obtain ⟨left⟩ := leftCut.canonical_far_output labels sourceClosed leftMore leftSnapshot
  obtain ⟨right⟩ := rightCut.canonical_far_output labels sourceClosed rightMore rightSnapshot
  refine ⟨left,right,?_⟩
  rcases paired_current_chain_source_labels initial prefixHistory old labels selected sourceSafe sourceClosed
      (labels.closed sourceClosed) left.currentChain right.currentChain iso left.nodeTrace right.nodeTrace with safe | same | opposite
  · obtain ⟨readSafe,es,fs,lc,rc,vector,oldIso⟩ := safe
    have le := lc.unique left.sourceChain
    have re := rc.unique right.sourceChain
    exact Or.inl ⟨readSafe,by simpa only [CanonicalFarFullComparison,←le,←re] using And.intro vector oldIso⟩
  · obtain ⟨lc,rc,sign,front,head,es,fs,leftChain,rightChain,vector,oldIso⟩ := same
    have le := leftChain.unique left.sourceChain
    have re := rightChain.unique right.sourceChain
    exact Or.inr (Or.inl ⟨lc,rc,sign,front,head,by simpa only [CanonicalFarFullComparison,←le,←re] using And.intro vector oldIso⟩)
  · exact Or.inr (Or.inr opposite)
end Lamping.AG
