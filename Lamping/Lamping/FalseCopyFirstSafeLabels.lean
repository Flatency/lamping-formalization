import Lamping.Lambda.UniformOldIncomingLabels
import Lamping.Lamping.ExpandedLastEndpointChains
import Lamping.Lambda.DirectedReadingDecomposition
namespace Lamping.Lambda.Marked
open Labelled

theorem equal_node_origin_labels_across_prefixes
    {F preL preR : List Path} {markedL markedR : Marked}
    {source middleL middleR nodeL nodeR : LTerm} {alpha : Label}
    {p q oldP oldQ : Path}
    (oldL : RelativeOldHistory F preL (mark F source.erase) markedL)
    (oldR : RelativeOldHistory F preR (mark F source.erase) markedR)
    (labelsL : Labelled.History preL source middleL)
    (labelsR : Labelled.History preR source middleR)
    (selected : ∀ name∈F, source.degreeAt name=some alpha)
    (sourceSafe : source.OuterBarsSafe (fun x => x≠alpha))
    (traceL : BetaNodeHistoryPreimage labelsL p oldP)
    (traceR : BetaNodeHistoryPreimage labelsR q oldQ)
    (lookupL : middleL.subterm p=some nodeL)
    (lookupR : middleR.subterm q=some nodeR)
    (sameIncoming : nodeL.label=nodeR.label) :
    ∃ originalL originalR,
      source.subterm oldP=some originalL ∧
      source.subterm oldQ=some originalR ∧
      originalL.label=originalR.label := by
  classical
  by_cases safe : nodeL.label.OuterBarsSafe (fun x=>x≠alpha)
  · have otherSafe : nodeR.label.OuterBarsSafe (fun x=>x≠alpha) := by rw [←sameIncoming];exact safe
    obtain ⟨originalL,atL,equalL⟩ :=
      (oldL.safe_incoming_uncreated (DegreeAligned.initial source F) selected traceL lookupL safe).source_label lookupL
    obtain ⟨originalR,atR,equalR⟩ :=
      (oldR.safe_incoming_uncreated (DegreeAligned.initial source F) selected traceR lookupR otherSafe).source_label lookupR
    exact ⟨originalL,originalR,atL,atR,equalL.trans (sameIncoming.trans equalR.symm)⟩
  · have otherMarked : ¬nodeR.label.OuterBarsSafe (fun x=>x≠alpha) := by rw [←sameIncoming];exact safe
    obtain ⟨originalL,preL,markerL,atL,safeL,marksL,equationL,reversedL⟩ :=
      oldL.node_last_marker (DegreeAligned.initial source F) labelsL selected traceL lookupL sourceSafe safe
    obtain ⟨originalR,preR,markerR,atR,safeR,marksR,equationR,reversedR⟩ :=
      oldR.node_last_marker (DegreeAligned.initial source F) labelsR selected traceR lookupR sourceSafe otherMarked
    have parsed := Label.readLetters_first_marker_of_splits (forward:=false)
      safeL safeR marksL marksR reversedL reversedR sameIncoming
    exact ⟨originalL,originalR,atL,atR,parsed.1⟩
end Lamping.Lambda.Marked

namespace Lamping.Lambda.Labelled
private theorem normal_expansion_end
    (expansion : CreatedReadingExpansion body site first last false es ds)
    (normal : ∃q : Path,q≠[] ∧last=(site++[.fn,.body])++q) : es.getLastD []=last := by
  cases expansion with
  | resultLambda =>
    obtain ⟨q,positive,same⟩:=normal
    have size:=congrArg List.length same
    simp at size
  | copyLambda => rfl
  | copyOverlap =>
    obtain ⟨q,positive,same⟩:=normal
    have empty : []=q:=List.append_cancel_left (by simpa only [List.append_nil] using same)
    exact False.elim (positive empty.symm)

private theorem normal_false_word
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge false)
    (lookup : target.subterm edge=some current)
    (normal : ∃q : Path,q≠[] ∧last=(site++[.fn,.body])++q)
    (expansion : CreatedReadingExpansion body site first last false es ds) :
    es.getLastD []=last ∧∃firstNode lastNode,
      source.subterm first=some firstNode ∧source.subterm last=some lastNode ∧
      current.label.readLetters false=firstNode.label.readLetters false++(.under alpha)::lastNode.label.readLetters false := by
  have endEq:=normal_expansion_end expansion normal
  obtain ⟨normalQ,positive,lastEq⟩:=normal
  cases origin with
  | resultFunction result function =>
    have size:=congrArg List.length (reading.2.symm.trans (result.trans function))
    simp at size
  | resultLambda result read shape =>
    have size:=congrArg List.length lastEq
    simp at size
  | @copyFunction parent occurs copy read =>
    have size:=congrArg List.length reading.2
    simp only [copy,read,List.length_append,List.length_singleton] at size
    omega
  | @copyLambda q stamp inner occurs copy read shape =>
    have qEq : q=normalQ:=List.append_cancel_left lastEq
    have nonroot : q≠[]:=by rw [qEq];exact positive
    subst argument
    have localLookup : (LTerm.contract beta alpha body (.lam stamp inner)).subterm q=some current := by
      rw [copy,LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at lookup
      exact lookup
    obtain ⟨variableStamp,oldLookup,labelEq⟩:=LTerm.contract_argument_incoming_label occurs localLookup
    rw [if_neg nonroot] at labelEq
    refine ⟨endEq,.lam stamp inner,.var variableStamp (binderDepth q),?_,?_,?_⟩
    · rw [LTerm.subterm_append,redex];rfl
    · rw [List.append_assoc,LTerm.subterm_append,redex]
      simpa only [LTerm.subterm,Option.bind_some] using oldLookup
    · change current.label.letters.reverse=stamp.letters.reverse++(.under alpha)::variableStamp.letters.reverse
      rw [labelEq]
      simp only [LTerm.label,Label.letters_concat,Label.under,Label.letters,List.reverse_append,
        List.reverse_cons,List.nil_append,List.cons_append,List.append_assoc]
end Lamping.Lambda.Labelled

namespace Lamping.AG
open Graph Lambda Lambda.Labelled SyntaxIncidence
section
variable {F ps : List Path} {source current leftHead rightHead : LTerm}
variable {alpha : Label}
variable {leftBefore rightBefore : List (Option Label)}
variable {leftEdge rightEdge : Path}
variable {leftSpine : DirectedMarkerSpine F source alpha false ps current leftBefore leftEdge}
variable {rightSpine : DirectedMarkerSpine F source alpha false ps current rightBefore rightEdge}
variable {leftLookup : current.subterm leftEdge=some leftHead}
variable {rightLookup : current.subterm rightEdge=some rightHead}
variable {leftLeaf : DirectedMarkerLeafOutput F source alpha false ps (leftHead.label.readLetters false)}
variable {rightLeaf : DirectedMarkerLeafOutput F source alpha false ps (rightHead.label.readLetters false)}
variable {leftSnapshot : IncomingIncidenceSnapshot current leftEdge}
variable {rightSnapshot : IncomingIncidenceSnapshot current rightEdge}
variable {leftGeometry : SpineIncidenceProvenance F source alpha false leftSpine leftLookup leftLeaf leftSnapshot}
variable {rightGeometry : SpineIncidenceProvenance F source alpha false rightSpine rightLookup rightLeaf rightSnapshot}

theorem recent_normal_false_copy_first_safe_labels
    (left : RecentSpineFrame leftGeometry) (right : RecentSpineFrame rightGeometry)
    (selected : ∀name∈F,source.degreeAt name=some alpha)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠alpha))
    (normalL : ∃q : Path,q≠[] ∧left.packet.last=(left.packet.site++[.fn,.body])++q)
    (normalR : ∃q : Path,q≠[] ∧right.packet.last=(right.packet.site++[.fn,.body])++q)
    (leftFirstSafe : ∀node,left.packet.middle.subterm left.packet.first=some node →node.label.OuterBarsSafe (fun x=>x≠alpha))
    (rightFirstSafe : ∀node,right.packet.middle.subterm right.packet.first=some node →node.label.OuterBarsSafe (fun x=>x≠alpha))
    {leftLast rightLast : LTerm}
    {leftOriginalFar rightOriginalFar : ProperPosition source} {leftFarEdges rightFarEdges : List Path}
    (leftOut : ExpandedLastOriginalEndpoints F source left.packet.middle alpha left.packet.event.labels
      (left.packet.frame.edges.getLastD []) leftLast false leftOriginalFar leftFarEdges)
    (rightOut : ExpandedLastOriginalEndpoints F source right.packet.middle alpha right.packet.event.labels
      (right.packet.frame.edges.getLastD []) rightLast false rightOriginalFar rightFarEdges)
    (leftLastLookup : left.packet.middle.subterm (left.packet.frame.edges.getLastD [])=some leftLast)
    (rightLastLookup : right.packet.middle.subterm (right.packet.frame.edges.getLastD [])=some rightLast)
    (sameHead : leftHead.label=rightHead.label) :
    ∃leftFirst rightFirst : LTerm,
      left.packet.middle.subterm left.packet.first=some leftFirst ∧
      right.packet.middle.subterm right.packet.first=some rightFirst ∧
      leftFirst.label=rightFirst.label ∧leftLast.label=rightLast.label ∧
      leftOut.original.label=rightOut.original.label ∧
      (leftLast.label.OuterBarsSafe (fun x=>x≠alpha) ↔rightLast.label.OuterBarsSafe (fun x=>x≠alpha)) := by
  obtain ⟨endL,firstL,lastL,atFirstL,atLastL,formulaL⟩:=normal_false_word
    left.packet.event.turn left.packet.event.redex left.packet.origin left.packet.reading left.packet.lookup normalL left.packet.frame.expansion
  obtain ⟨endR,firstR,lastR,atFirstR,atLastR,formulaR⟩:=normal_false_word
    right.packet.event.turn right.packet.event.redex right.packet.origin right.packet.reading right.packet.lookup normalR right.packet.frame.expansion
  have lastLEq : lastL=leftLast:=Option.some.inj (atLastL.symm.trans (endL ▸ leftLastLookup))
  have lastREq : lastR=rightLast:=Option.some.inj (atLastR.symm.trans (endR ▸ rightLastLookup))
  subst lastL;subst lastR
  obtain ⟨oldL,atL,labelL⟩:=left.uncreatedSuffix.source_label leftLookup
  obtain ⟨oldR,atR,labelR⟩:=right.uncreatedSuffix.source_label rightLookup
  have currentL : oldL=left.packet.current:=Option.some.inj (atL.symm.trans left.packet.lookup)
  have currentR : oldR=right.packet.current:=Option.some.inj (atR.symm.trans right.packet.lookup)
  have sameCurrent : left.packet.current.label=right.packet.current.label := by
    rw [←currentL,←currentR];exact labelL.trans (sameHead.trans labelR.symm)
  have parsed:=Label.readLetters_first_marker_of_splits (forward:=false)
    (leftFirstSafe _ atFirstL) (rightFirstSafe _ atFirstR)
    (show (Letter.under alpha).MarksDegree alpha from Or.inr rfl)
    (show (Letter.under alpha).MarksDegree alpha from Or.inr rfl) formulaL formulaR sameCurrent
  have sameLast : leftLast.label=rightLast.label:=Label.readLetters_injective parsed.2.2
  obtain ⟨originalL,originalR,atOriginalL,atOriginalR,originalEq⟩:=
    Marked.equal_node_origin_labels_across_prefixes left.packet.event.beforeOld right.packet.event.beforeOld
      left.packet.event.labels right.packet.event.labels selected sourceSafe leftOut.nodeTrace rightOut.nodeTrace
      leftLastLookup rightLastLookup sameLast
  have oldLEq : originalL=leftOut.original:=Option.some.inj (atOriginalL.symm.trans leftOut.lookup)
  have oldREq : originalR=rightOut.original:=Option.some.inj (atOriginalR.symm.trans rightOut.lookup)
  refine ⟨firstL,firstR,atFirstL,atFirstR,parsed.1,sameLast,?_,?_⟩
  · simpa only [oldLEq,oldREq] using originalEq
  · rw [sameLast]
end
#print axioms Marked.equal_node_origin_labels_across_prefixes
#print axioms recent_normal_false_copy_first_safe_labels
end Lamping.AG
