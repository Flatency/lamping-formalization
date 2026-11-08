import Lamping.Lamping.ExpandedArgumentHistoryOrigins
import Lamping.Lambda.AuxiliaryNodeHistoryOrigins
import Lamping.Lambda.ActualNodeLabelAncestry

namespace Lamping.Lambda.Labelled
open SyntaxIncidence
variable {source middle target body argument : LTerm}

private theorem result_position
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

/-- All actual TRUE expansions end at the old node ancestor, including
ordinary RESULT's retained BODY root. No statement is made for FALSE. -/
theorem BetaIncomingReadingOrigin.forward_expanded_last_node_preimage
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (expansion : CreatedReadingExpansion body site first last true edges directions) :
    BetaNodePreimage body argument site edge (edges.getLastD []) := by
  cases expansion with
  | resultFunction other =>
    have position:=result_position origin rfl
    rw [position]
    have rootLookup : body.subterm []=some body := by cases body <;> rfl
    have notSelected : ∀stamp,body≠.var stamp (binderDepth []) := by
      intro stamp
      simpa only [binderDepth] using other stamp
    simpa only [List.append_nil,List.getLastD_cons,List.getLastD_nil] using
      (BetaNodePreimage.retained (site:=site) (relative:=[]) rootLookup notSelected)
  | resultOverlap shape =>
    exact origin.expanded_argument_node_preimage (.resultOverlap shape) rfl
  | copyFunction =>
    exact origin.expanded_argument_node_preimage .copyFunction rfl

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

/-- This GIVEN recent frame supplies the full actual history preimage
without a caller ARG-end condition or safety at the expanded LAST. -/
theorem RecentSpineFrame.forward_expanded_last_history_preimage
    (recent : RecentSpineFrame geometry) (labels : History ps source target)
    {lastNode : LTerm} {originalFar : ProperPosition source} {farEdges : List Path}
    (out : Lamping.AG.ExpandedLastOriginalEndpoints F source recent.packet.middle degree
      recent.packet.event.labels (recent.packet.frame.edges.getLastD []) lastNode true originalFar farEdges) :
    BetaNodeHistoryPreimage labels edge out.oldEdge := by
  have one:=recent.packet.origin.forward_expanded_last_node_preimage recent.packet.frame.expansion
  have suffix:=recent.uncreatedSuffix.to_node
  have eventAndSuffix : BetaNodeHistoryPreimage (.cons recent.packet.event.turn recent.suffixHistory)
      edge (recent.packet.frame.edges.getLastD []) :=
    .one (step:=recent.packet.event.turn) recent.packet.event.redex one suffix
  have full:=append_origins out.nodeTrace eventAndSuffix
  have schedule : recent.packet.pre++(recent.packet.site::recent.suffixSites)=ps := by
    simpa only [List.append_assoc,List.singleton_append] using recent.schedule.symm
  exact reindex_origins schedule labels full
end

#print axioms BetaIncomingReadingOrigin.forward_expanded_last_node_preimage
#print axioms RecentSpineFrame.forward_expanded_last_history_preimage
end Lamping.Lambda.Labelled

namespace Lamping.AG
open Lambda Lambda.Labelled SyntaxIncidence
variable {source target : LTerm}

private theorem forward_last_role
    (expansion : CreatedReadingExpansion body site first last true edges directions) :
    edges.getLastD []=site++[.fn,.body] ∨edges.getLastD []=site++[.arg] := by
  cases expansion with
  | resultFunction => exact Or.inl rfl
  | resultOverlap => exact Or.inr rfl
  | copyFunction => exact Or.inr rfl

private theorem nonlambda_of_tag {old current : LTerm}
    (same : old.constructorTag=current.constructorTag)
    (notLambda : ∀a b,current≠.lam a b) : ∀a b,old≠.lam a b := by
  intro a b equal
  subst old
  cases current with
  | var => cases same
  | app => cases same
  | lam stamp inner => exact notLambda stamp inner rfl

private theorem nonterminal_true_head_not_lambda
    (cut : ActualUnsafeMarkerCut F ps source target degree start es)
    (positive : cut.forward=true) (nonterminal : cut.after≠[]) :
    ∀a b,cut.node≠.lam a b := by
  intro a b equal
  have read : PrerequisiteReadsDirected target cut.reader cut.edge true := positive ▸ cut.reading
  have edgeRedex : PrerequisiteRedexEdge target cut.edge := by
    rcases read.1 with ⟨stamp,fn,arg,atApp,split⟩ | ⟨stamp,body,atLambda,split⟩
    · have fnLookup : target.subterm cut.edge=some fn := by
        rw [split,LTerm.subterm_append,atApp]
        cases fn <;> rfl
      have shape : fn=.lam a b := Option.some.inj (fnLookup.symm.trans (equal ▸ cut.lookup))
      exact ⟨cut.reader,stamp,a,b,arg,split,shape ▸ atApp⟩
    · have lengths:=congrArg List.length (split.symm.trans read.2)
      simp at lengths
  obtain ⟨before,last,split,_redex,earlier⟩:=cut.remaining.redex_only_last
  cases beforeEq : before with
  | nil =>
    rw [beforeEq,List.nil_append] at split
    exact nonterminal (List.cons.inj split).2
  | cons first rest =>
    rw [beforeEq,List.cons_append] at split
    have headEq:= (List.cons.inj split).1
    exact earlier cut.edge (by rw [beforeEq,headEq];simp) edgeRedex

private theorem recent_forward_last_auxiliary
    {F : List Path} {source target current : LTerm} {degree : Label} {forward : Bool}
    {ps : List Path} {beforeLabels : List (Option Label)} {edge : Path}
    {spine : DirectedMarkerSpine F source degree forward ps target beforeLabels edge}
    {lookup : target.subterm edge=some current}
    {leaf : DirectedMarkerLeafOutput F source degree forward ps (current.label.readLetters forward)}
    {snapshot : IncomingIncidenceSnapshot target edge}
    {geometry : SpineIncidenceProvenance F source degree forward spine lookup leaf snapshot}
    (recent : RecentSpineFrame geometry) (positive : forward=true)
    (notLambda : ∀a b,current≠.lam a b) :
    ∃lastNode,recent.packet.middle.subterm (recent.packet.frame.edges.getLastD [])=some lastNode ∧
      AuxiliaryAt recent.packet.middle (recent.packet.frame.edges.getLastD []) := by
  cases forward with
  | false => cases positive
  | true =>
    obtain ⟨packetNode,packetAt,_last,tag⟩:=recent.uncreatedSuffix.to_node.lastAtom_constructor lookup
    have packetEq : packetNode=recent.packet.current :=
      Option.some.inj (packetAt.symm.trans recent.packet.lookup)
    rw [packetEq] at tag
    have origin:=recent.packet.origin.forward_expanded_last_node_preimage recent.packet.frame.expansion
    obtain ⟨lastNode,lastAt,lastTag⟩:=recent.packet.event.turn.preimage_node_constructor
      recent.packet.event.redex origin recent.packet.lookup
    have lastNotLambda:=nonlambda_of_tag (lastTag.trans tag) notLambda
    have lastRole:=forward_last_role recent.packet.frame.expansion
    refine ⟨lastNode,lastAt,?_,?_⟩
    · have notFunction : (recent.packet.frame.edges.getLastD []).getLast?≠some .fn := by
        rcases lastRole with body | arg
        · rw [body];simp
        · rw [arg];simp
      rintro ⟨parent,stamp,fn,arg,split,_atApp⟩
      exact notFunction (by rw [split,List.getLast?_concat])
    · rintro ⟨stamp,body,atLambda⟩
      exact lastNotLambda stamp body (Option.some.inj (lastAt.symm.trans atLambda))

section
variable {F ps : List Path} {source target : LTerm} {degree : Label} {start : Path} {es : List Path}
variable {cut : ActualUnsafeMarkerCut F ps source target degree start es}
variable {leaf : DirectedMarkerLeafOutput F source degree cut.forward ps (cut.node.label.readLetters cut.forward)}
variable {snapshot : IncomingIncidenceSnapshot target cut.edge}
variable {geometry : SpineIncidenceProvenance F source degree cut.forward cut.spine cut.lookup leaf snapshot}

/-- Nonterminal TRUE reads internally make the actual expanded LAST and
its original SOURCE ancestor auxiliary, without a safe-LAST premise. -/
theorem ActualUnsafeMarkerCut.forward_original_last_auxiliary
    (positive : cut.forward=true) (nonterminal : cut.after≠[])
    (recent : RecentSpineFrame geometry)
    {lastNode : LTerm} {originalFar : ProperPosition source} {farEdges : List Path}
    (out : ExpandedLastOriginalEndpoints F source recent.packet.middle degree
      recent.packet.event.labels (recent.packet.frame.edges.getLastD []) lastNode cut.forward originalFar farEdges) :
    AuxiliaryAt source out.oldEdge := by
  obtain ⟨middleNode,middleAt,middleAux⟩:=recent_forward_last_auxiliary recent positive
    (nonterminal_true_head_not_lambda cut positive nonterminal)
  obtain ⟨_original,_originalAt,originalAux⟩:=out.nodeTrace.auxiliary_source middleAt middleAux
  exact originalAux
end

#print axioms ActualUnsafeMarkerCut.forward_original_last_auxiliary
end Lamping.AG

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

/-- All TRUE indexed outputs. The two actual recent prefixes may differ.
The new full traces give old ARG labels and SOURCE successful iso, without
claiming TARGET iso or equality of marked local physical evaluators. -/
theorem recent_forward_expanded_last_source_comparison
    (left : RecentSpineFrame leftGeometry) (right : RecentSpineFrame rightGeometry)
    (labels : History ps source target)
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
  have leftTrace := left.forward_expanded_last_history_preimage labels leftOut
  have rightTrace := right.forward_expanded_last_history_preimage labels rightOut
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
#print axioms recent_forward_expanded_last_source_comparison
end Lamping.AG
