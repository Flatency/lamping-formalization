import Lamping.Lamping.ExpandedLastEndpointChains
import Lamping.Lamping.MarkedOldSourceEndpointIso
import Lamping.Lambda.UniformOldIncomingLabels

namespace Lamping.Lambda.Labelled
open SyntaxIncidence
variable {source middle target body argument : LTerm}

private theorem argument_root_preimage
    (occurs : ArgumentOccurrence body.erase q) :
    BetaNodePreimage body argument site (site++q) (site++[.arg]) := by
  have lookup : argument.subterm []=some argument := by cases argument <;> rfl
  simpa only [List.append_nil] using
    (BetaNodePreimage.copied (site:=site) (relative:=[]) occurs lookup)

private theorem result_position_of_first_site
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (same : first=site) : edge=site := by
  cases origin with
  | resultFunction result _ => exact result
  | resultLambda =>
    have lengths:=congrArg List.length same
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega
  | copyFunction =>
    have lengths:=congrArg List.length same
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega
  | copyLambda =>
    have lengths:=congrArg List.length same
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega

private theorem preimage_of_last_argument
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (same : last=site++[.arg]) :
    BetaNodePreimage body argument site edge (site++[.arg]) := by
  cases origin with
  | resultFunction =>
    have lengths:=congrArg List.length same
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega
  | resultLambda =>
    have lengths:=congrArg List.length same
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega
  | copyFunction occurs copy _ =>
    rw [copy]
    exact argument_root_preimage occurs
  | copyLambda =>
    have lengths:=congrArg List.length same
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega

/-- A forward creation away from the result root has an actual expanded
ARG end. This derives a finite role condition from real coordinates. -/
theorem BetaIncomingReadingOrigin.expanded_argument_end_of_nonresult
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (expansion : CreatedReadingExpansion body site first last true edges directions)
    (nonresult : edge≠site) : edges.getLastD []=site++[.arg] := by
  cases expansion with
  | resultFunction other => exact False.elim (nonresult (result_position_of_first_site origin rfl))
  | resultOverlap shape => rfl
  | copyFunction => rfl

/-- Only the actual TRUE expanded final ARG is a copied-node ancestor.
The RESULTvar0 overlap uses ARG, not its BODYvar triple LAST. -/
theorem BetaIncomingReadingOrigin.expanded_argument_node_preimage
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (expansion : CreatedReadingExpansion body site first last true edges directions)
    (endIsArgument : edges.getLastD []=site++[.arg]) :
    BetaNodePreimage body argument site edge (edges.getLastD []) := by
  cases expansion with
  | resultFunction other =>
    have lengths:=congrArg List.length endIsArgument
    simp only [List.getLastD_cons,List.getLastD_nil,List.length_append,List.length_cons,List.length_nil] at lengths
    omega
  | resultOverlap shape =>
    have position:=result_position_of_first_site origin rfl
    rw [endIsArgument,position]
    have occurs : ArgumentOccurrence body.erase [] := by
      rw [shape]
      rfl
    simpa only [List.append_nil] using argument_root_preimage (site:=site) (argument:=argument) occurs
  | copyFunction =>
    rw [endIsArgument]
    exact preimage_of_last_argument origin rfl

private theorem append_origins
    {firstHistory : History ps source middle} {lastHistory : History qs middle target}
    (first : BetaNodeHistoryPreimage firstHistory middleEdge oldEdge)
    (last : BetaNodeHistoryPreimage lastHistory edge middleEdge) :
    BetaNodeHistoryPreimage (firstHistory.append lastHistory) edge oldEdge := by
  induction first with
  | nil => exact last
  | @one _ _ _ _ _ _ _ _ _ _ _ _ step _ redex origin tail ih =>
    exact .one (step:=step) redex origin (ih last)

private theorem reindex_origins {ps qs : List Path}
    (same : ps=qs) {labels : History ps source target} (other : History qs source target)
    (trace : BetaNodeHistoryPreimage labels edge oldEdge) : BetaNodeHistoryPreimage other edge oldEdge := by
  subst qs
  exact trace

section
variable {F : List Path} {source target current : LTerm} {degree : Label}
variable {ps : List Path} {beforeLabels : List (Option Label)} {edge : Path}
variable {spine : DirectedMarkerSpine F source degree true ps target beforeLabels edge}
variable {lookup : target.subterm edge=some current}
variable {leaf : DirectedMarkerLeafOutput F source degree true ps (current.label.readLetters true)}
variable {snapshot : IncomingIncidenceSnapshot target edge}
variable {geometry : SpineIncidenceProvenance F source degree true spine lookup leaf snapshot}

/-- Compose THIS recent frame's actual prefix/event/inherited suffix.
This low adapter consumes the indexed endpoint producer result; it does not
identify an arbitrary OTHERLAST, require a safe LAST, or compare local values. -/
theorem RecentSpineFrame.expanded_argument_history_preimage
    (recent : RecentSpineFrame geometry) (labels : History ps source target)
    (endIsArgument : recent.packet.frame.edges.getLastD []=recent.packet.site++[.arg])
    {lastNode : LTerm} {originalFar : ProperPosition source} {farEdges : List Path}
    (out : Lamping.AG.ExpandedLastOriginalEndpoints F source recent.packet.middle degree
      recent.packet.event.labels (recent.packet.frame.edges.getLastD []) lastNode true originalFar farEdges) :
    BetaNodeHistoryPreimage labels edge out.oldEdge := by
  have one := recent.packet.origin.expanded_argument_node_preimage recent.packet.frame.expansion endIsArgument
  have suffix := recent.uncreatedSuffix.to_node
  have eventAndSuffix : BetaNodeHistoryPreimage (.cons recent.packet.event.turn recent.suffixHistory)
      edge (recent.packet.frame.edges.getLastD []) :=
    .one (step:=recent.packet.event.turn) recent.packet.event.redex one suffix
  have full := append_origins out.nodeTrace eventAndSuffix
  have schedule : recent.packet.pre++(recent.packet.site::recent.suffixSites)=ps := by
    simpa only [List.append_assoc,List.singleton_append] using recent.schedule.symm
  exact reindex_origins schedule labels full
end

#print axioms BetaIncomingReadingOrigin.expanded_argument_node_preimage
#print axioms BetaIncomingReadingOrigin.expanded_argument_end_of_nonresult
#print axioms RecentSpineFrame.expanded_argument_history_preimage
end Lamping.Lambda.Labelled

namespace Lamping.AG
open Lambda Lambda.Labelled SyntaxIncidence
section
variable {F ps : List Path} {source target leftNode rightNode : LTerm} {degree : Label}
variable {leftBefore rightBefore : List (Option Label)} {leftEdge rightEdge : Path}
variable {leftSpine : DirectedMarkerSpine F source degree true ps target leftBefore leftEdge}
variable {rightSpine : DirectedMarkerSpine F source degree true ps target rightBefore rightEdge}
variable {leftLookup : target.subterm leftEdge=some leftNode}
variable {rightLookup : target.subterm rightEdge=some rightNode}
variable {leftLeaf : DirectedMarkerLeafOutput F source degree true ps (leftNode.label.readLetters true)}
variable {rightLeaf : DirectedMarkerLeafOutput F source degree true ps (rightNode.label.readLetters true)}
variable {leftSnapshot : IncomingIncidenceSnapshot target leftEdge}
variable {rightSnapshot : IncomingIncidenceSnapshot target rightEdge}
variable {leftGeometry : SpineIncidenceProvenance F source degree true leftSpine leftLookup leftLeaf leftSnapshot}
variable {rightGeometry : SpineIncidenceProvenance F source degree true rightSpine rightLookup rightLeaf rightSnapshot}

/-- Low indexed-output adapter. The two actual recent prefixes may differ.
The new full traces give old ARG labels and SOURCE successful iso, without
claiming TARGET iso or equality of marked local physical evaluators. -/
theorem recent_expanded_argument_source_comparison
    (left : RecentSpineFrame leftGeometry) (right : RecentSpineFrame rightGeometry)
    (labels : History ps source target)
    (leftArg : left.packet.frame.edges.getLastD []=left.packet.site++[.arg])
    (rightArg : right.packet.frame.edges.getLastD []=right.packet.site++[.arg])
    {leftLast rightLast : LTerm} {leftFar rightFar : ProperPosition source}
    {leftFarEdges rightFarEdges : List Path}
    (leftOut : ExpandedLastOriginalEndpoints F source left.packet.middle degree left.packet.event.labels
      (left.packet.frame.edges.getLastD []) leftLast true leftFar leftFarEdges)
    (rightOut : ExpandedLastOriginalEndpoints F source right.packet.middle degree right.packet.event.labels
      (right.packet.frame.edges.getLastD []) rightLast true rightFar rightFarEdges)
    {marked : Marked}
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) marked)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (closed : Closed source.erase)
    (leftMarked : ¬leftNode.label.OuterBarsSafe (fun x=>x≠degree))
    (rightMarked : ¬rightNode.label.OuterBarsSafe (fun x=>x≠degree))
    (same : leftNode.label=rightNode.label) :
    leftOut.original.label=rightOut.original.label ∧
      SuccessfulEndpointIso source closed (some leftOut.fromVertex) (some rightOut.fromVertex) := by
  have leftTrace := left.expanded_argument_history_preimage labels leftArg leftOut
  have rightTrace := right.expanded_argument_history_preimage labels rightArg rightOut
  obtain ⟨ln,rn,ll,rl,equal⟩ := old.equal_node_origin_labels (DegreeAligned.initial source F)
    labels selected leftTrace rightTrace leftLookup rightLookup sourceSafe same
  have leftEq := Option.some.inj (leftOut.lookup.symm.trans ll)
  have rightEq := Option.some.inj (rightOut.lookup.symm.trans rl)
  have labelsEqual : leftOut.original.label=rightOut.original.label := by
    rw [leftEq,rightEq]
    exact equal
  exact ⟨labelsEqual,marked_old_source_endpoint_iso closed old selected leftTrace rightTrace
    leftLookup rightLookup sourceSafe leftMarked rightMarked leftOut.sourceSpec rightOut.sourceSpec⟩
end
#print axioms recent_expanded_argument_source_comparison
end Lamping.AG
