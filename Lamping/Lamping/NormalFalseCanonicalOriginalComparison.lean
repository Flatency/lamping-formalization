import Lamping.Lamping.FalseCopyFirstSafeLabels
import Lamping.Lamping.ForwardCanonicalOriginalFragments
namespace Lamping.Lambda.Labelled
open SyntaxIncidence
variable {source target current : LTerm}

private theorem normal_copy_shape
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (redex : source.subterm site=some (.app beta (.lam degree body) argument))
    (normal : ∃q : Path,q≠[] ∧last=(site++[.fn,.body])++q) :
    ∃q stamp,q≠[] ∧edge=site++q ∧last=(site++[.fn,.body])++q ∧
      source.subterm last=some (.var stamp (binderDepth q)) := by
  obtain ⟨actual,positive,lastEq⟩:=normal
  cases origin with
  | resultFunction =>
    have nil : []=actual:=List.append_cancel_left (by simpa only [List.append_nil] using lastEq)
    exact False.elim (positive nil.symm)
  | resultLambda =>
    have size:=congrArg List.length lastEq
    simp only [List.length_append,List.length_cons,List.length_nil] at size
    omega
  | copyFunction =>
    have size:=congrArg List.length lastEq
    simp only [List.length_append,List.length_cons,List.length_nil] at size
    omega
  | @copyLambda q stamp inner occurs copy read shape =>
    have same : q=actual:=List.append_cancel_left lastEq
    have nonempty : q≠[]:=by rw [same];exact positive
    change subtermAt body.erase q=some (.var (binderDepth q)) at occurs
    rw [←LTerm.erase_subterm] at occurs
    obtain ⟨node,lookup,erased⟩:=Option.map_eq_some_iff.mp occurs
    cases node with
    | var label index =>
      cases erased
      refine ⟨q,label,nonempty,copy,rfl,?_⟩
      rw [List.append_assoc,LTerm.subterm_append,redex]
      exact lookup
    | app => cases erased
    | lam => cases erased

private theorem normal_direction
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge forward)
    (normal : ∃q : Path,q≠[] ∧last=(site++[.fn,.body])++q) : forward=false := by
  obtain ⟨q,positive,lastEq⟩:=normal
  cases origin with
  | resultFunction =>
    have nil : []=q:=List.append_cancel_left (by simpa only [List.append_nil] using lastEq)
    exact False.elim (positive nil.symm)
  | resultLambda =>
    have size:=congrArg List.length lastEq
    simp only [List.length_append,List.length_cons,List.length_nil] at size
    omega
  | copyFunction =>
    have size:=congrArg List.length lastEq
    simp only [List.length_append,List.length_cons,List.length_nil] at size
    omega
  | copyLambda _ _ read _ =>
    cases forward with
    | false => rfl
    | true =>
      have size:=congrArg List.length (read.trans reading.2)
      simp at size

private theorem normal_expansion_end
    (expansion : CreatedReadingExpansion body site first last forward es ds)
    (normal : ∃q : Path,q≠[] ∧last=(site++[.fn,.body])++q) : es.getLastD []=last := by
  cases expansion with
  | resultFunction =>
    obtain ⟨q,positive,lastEq⟩:=normal
    have nil : []=q:=List.append_cancel_left (by simpa only [List.append_nil] using lastEq)
    exact False.elim (positive nil.symm)
  | resultOverlap =>
    obtain ⟨q,positive,lastEq⟩:=normal
    have nil : []=q:=List.append_cancel_left (by simpa only [List.append_nil] using lastEq)
    exact False.elim (positive nil.symm)
  | copyFunction =>
    obtain ⟨q,positive,lastEq⟩:=normal
    have size:=congrArg List.length lastEq
    simp only [List.length_append,List.length_cons,List.length_nil] at size
    omega
  | resultLambda =>
    obtain ⟨q,positive,lastEq⟩:=normal
    have size:=congrArg List.length lastEq
    simp only [List.length_append,List.length_cons,List.length_nil] at size
    omega
  | copyLambda => rfl
  | copyOverlap =>
    obtain ⟨q,positive,lastEq⟩:=normal
    have nil : []=q:=List.append_cancel_left (by simpa only [List.append_nil] using lastEq)
    exact False.elim (positive nil.symm)

private theorem uncreated_last
    {labels : History ps source target}
    (trace : UncreatedNodeHistoryPreimage labels edge old) : edge.getLast?=old.getLast? := by
  induction trace with
  | nil => rfl
  | one redex origin uncreated tail ih => exact ih.trans (origin.uncreated_last_step uncreated)

private theorem append_last {A : Type} (pre : List A) {rest : List A} (positive : rest≠[]) :
    (pre++rest).getLast?=rest.getLast? := by
  have last:=List.getLast?_eq_some_getLast positive
  simp only [List.getLast?_append,last,Option.some_or]
end Lamping.Lambda.Labelled

namespace Lamping.AG
open Graph Lambda Lambda.Labelled SyntaxIncidence
variable {source current : LTerm}

private theorem nonterminal_not_redex
    (chain : PrerequisiteChain t start (edge::after)) (more : after≠[]) :
    ¬PrerequisiteRedexEdge t edge := by
  obtain ⟨before,last,split,_redex,earlier⟩:=chain.redex_only_last
  cases before with
  | nil =>
    simp only [List.nil_append,List.cons.injEq] at split
    exact False.elim (more split.2)
  | cons head tail =>
    have same : edge=head:=(List.cons.inj split).1
    exact earlier edge (by rw [same];exact List.mem_cons_self)

private theorem first_bad_unique {A : Type} (P : A→Prop)
    {bs cs : List A} {e f : A} {as ds : List A}
    (same : bs++e::as=cs++f::ds)
    (leftSafe : ∀x∈bs,P x) (rightSafe : ∀x∈cs,P x)
    (leftBad : ¬P e) (rightBad : ¬P f) : bs=cs ∧e=f ∧as=ds := by
  induction bs generalizing cs with
  | nil =>
    cases cs with
    | nil => exact ⟨rfl,(List.cons.inj same).1,(List.cons.inj same).2⟩
    | cons head tail =>
      have eq : e=head:=(List.cons.inj same).1
      exact False.elim (leftBad (eq ▸ rightSafe head List.mem_cons_self))
  | cons head tail ih =>
    cases cs with
    | nil =>
      have eq : head=f:=(List.cons.inj same).1
      exact False.elim (rightBad (eq ▸ leftSafe head List.mem_cons_self))
    | cons other rest =>
      have parts:=List.cons.inj same
      have answer:=ih parts.2 (fun x inside=>leftSafe x (List.mem_cons_of_mem _ inside))
        (fun x inside=>rightSafe x (List.mem_cons_of_mem _ inside))
      exact ⟨by rw [parts.1,answer.1],answer.2⟩

private theorem cut_bad (cut : ActualUnsafeMarkerCut F ps source current degree start edges) :
    ¬degreeReadSafe degree (current.labelAt cut.edge) := by
  intro safe
  exact cut.marked (safe cut.node.label (by simp only [LTerm.labelAt,cut.lookup,Option.map_some]))

private theorem cut_lists
    (left right : ActualUnsafeMarkerCut F ps source current degree start edges) :
    left.before=right.before ∧left.edge=right.edge ∧left.after=right.after := by
  exact first_bad_unique (fun p=>degreeReadSafe degree (current.labelAt p))
    (left.split.symm.trans right.split) left.safeBefore right.safeBefore (cut_bad left) (cut_bad right)

private theorem cut_data_ext
    (left right : ActualUnsafeMarkerCut F ps source current degree start edges)
    (before : left.before=right.before) (edge : left.edge=right.edge)
    (after : left.after=right.after) (reader : left.reader=right.reader)
    (node : left.node=right.node) (direction : left.forward=right.forward) : left=right := by
  cases left
  cases right
  cases before
  cases edge
  cases after
  cases reader
  cases node
  cases direction
  rfl

private theorem cut_unique
    (left right : ActualUnsafeMarkerCut F ps source current degree start edges)
    (more : left.after≠[]) (direction : left.forward=false) : left=right := by
  obtain ⟨front,head,tail⟩:=cut_lists left right
  have rightMore : right.after≠[]:=fun empty=>more (tail.trans empty)
  have dirs:=left.reading.nonredex_direction_eq right.reading
    (nonterminal_not_redex left.remaining more) (nonterminal_not_redex right.remaining rightMore)
    (congrArg List.getLast? head)
  have ld : left.edge=left.reader := by simpa only [direction] using left.reading.2
  have rd : right.edge=right.reader := by simpa only [←dirs,direction] using right.reading.2
  have readers : left.reader=right.reader:=ld.symm.trans (head.trans rd)
  have nodes : left.node=right.node:=Option.some.inj (left.lookup.symm.trans (head ▸ right.lookup))
  exact cut_data_ext left right front head tail readers nodes dirs

section
variable {source current : LTerm} {F ps : List Path} {degree : Label}
variable {start : Path} {edges : List Path}
variable {cut : ActualUnsafeMarkerCut F ps source current degree start edges}
variable {snapshot : IncomingIncidenceSnapshot current cut.edge}
variable {leaf : DirectedMarkerLeafOutput F source degree cut.forward ps (cut.node.label.readLetters cut.forward)}
variable {geometry : SpineIncidenceProvenance F source degree cut.forward cut.spine cut.lookup leaf snapshot}

private theorem normal_original_aux
    (recent : RecentSpineFrame geometry) (more : cut.after≠[])
    (normal : ∃q : Path,q≠[] ∧recent.packet.last=(recent.packet.site++[.fn,.body])++q)
    {lastNode : LTerm} {originalFar : ProperPosition source} {farEdges : List Path}
    (out : ExpandedLastOriginalEndpoints F source recent.packet.middle degree recent.packet.event.labels
      (recent.packet.frame.edges.getLastD []) lastNode cut.forward originalFar farEdges) :
    AuxiliaryAt source out.oldEdge := by
  have direction : cut.forward=false:=normal_direction recent.packet.origin recent.packet.reading normal
  have notFn : cut.edge.getLast?≠some .fn := by
    intro fn
    have pos:cut.forward=true:=(cut.reading.nonredex_forward_iff_function
      (nonterminal_not_redex cut.remaining more)).mpr fn
    rw [direction] at pos
    cases pos
  have packetNotFn : recent.packet.edge.getLast?≠some .fn := by
    rw [←uncreated_last recent.uncreatedSuffix]
    exact notFn
  obtain ⟨q,stamp,positive,edgeEq,lastEq,lastLookup⟩:=normal_copy_shape
    recent.packet.origin recent.packet.event.redex normal
  have lastNotFn : recent.packet.last.getLast?≠some .fn := by
    rw [lastEq,append_last _ positive]
    have role:=packetNotFn
    rw [edgeEq,append_last _ positive] at role
    exact role
  have middleAux : AuxiliaryAt recent.packet.middle recent.packet.last := by
    constructor
    · rintro ⟨parent,a,fn,arg,split,_atParent⟩
      exact lastNotFn (by rw [split,List.getLast?_concat])
    · rintro ⟨a,b,atLambda⟩
      rw [lastLookup] at atLambda
      cases atLambda
  have endEq:=normal_expansion_end recent.packet.frame.expansion normal
  have actualAux : AuxiliaryAt recent.packet.middle (recent.packet.frame.edges.getLastD []):=by rw [endEq];exact middleAux
  have actualLookup : recent.packet.middle.subterm (recent.packet.frame.edges.getLastD [])=some (.var stamp (binderDepth q)):=by rw [endEq];exact lastLookup
  exact (out.nodeTrace.auxiliary_source actualLookup actualAux).choose_spec.2
end

private theorem selected_iso
    (closed : Closed source.erase)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (left : SelectedOriginalSingleton F source degree lv les)
    (right : SelectedOriginalSingleton F source degree rv res)
    (lc : EndpointChain source (some lv) les) (rc : EndpointChain source (some rv) res) :
    SuccessfulEndpointIso source closed (some lv) (some rv) := by
  obtain ⟨ln,lm,lb,lbody,larg,lat,_lp,le⟩:=left
  obtain ⟨rn,rm,rb,rbody,rarg,rat,_rp,re⟩:=right
  refine ⟨les,res,lc,rc,?_⟩
  rw [le,re]
  exact (redex_chain_iso_iff_degree closed lat rat).mpr ((selected ln lm).trans (selected rn rm).symm)

private theorem bool_normal_labels
    {F ps : List Path} {source current leftNode rightNode : LTerm} {degree : Label}
    {ld rd : Bool} {lb rb : List (Option Label)} {le re : Path}
    {ls : DirectedMarkerSpine F source degree ld ps current lb le}
    {rs : DirectedMarkerSpine F source degree rd ps current rb re}
    {ll : current.subterm le=some leftNode} {rl : current.subterm re=some rightNode}
    {lf : DirectedMarkerLeafOutput F source degree ld ps (leftNode.label.readLetters ld)}
    {rf : DirectedMarkerLeafOutput F source degree rd ps (rightNode.label.readLetters rd)}
    {ln : IncomingIncidenceSnapshot current le} {rn : IncomingIncidenceSnapshot current re}
    {lg : SpineIncidenceProvenance F source degree ld ls ll lf ln}
    {rg : SpineIncidenceProvenance F source degree rd rs rl rf rn}
    (left : RecentSpineFrame lg) (right : RecentSpineFrame rg)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (safe : source.OuterBarsSafe (fun x=>x≠degree))
    (normalL : ∃q : Path,q≠[] ∧left.packet.last=(left.packet.site++[.fn,.body])++q)
    (normalR : ∃q : Path,q≠[] ∧right.packet.last=(right.packet.site++[.fn,.body])++q)
    (firstSafeL : ∀node,left.packet.middle.subterm left.packet.first=some node →node.label.OuterBarsSafe (fun x=>x≠degree))
    (firstSafeR : ∀node,right.packet.middle.subterm right.packet.first=some node →node.label.OuterBarsSafe (fun x=>x≠degree))
    {lastL lastR : LTerm} {farL farR : ProperPosition source} {es fs : List Path}
    (outL : ExpandedLastOriginalEndpoints F source left.packet.middle degree left.packet.event.labels
      (left.packet.frame.edges.getLastD []) lastL ld farL es)
    (outR : ExpandedLastOriginalEndpoints F source right.packet.middle degree right.packet.event.labels
      (right.packet.frame.edges.getLastD []) lastR rd farR fs)
    (atL : left.packet.middle.subterm (left.packet.frame.edges.getLastD [])=some lastL)
    (atR : right.packet.middle.subterm (right.packet.frame.edges.getLastD [])=some lastR)
    (head : leftNode.label=rightNode.label) (falseL : ld=false) (falseR : rd=false) :
    ∃firstL firstR,left.packet.middle.subterm left.packet.first=some firstL ∧
      right.packet.middle.subterm right.packet.first=some firstR ∧firstL.label=firstR.label ∧
      lastL.label=lastR.label ∧outL.original.label=outR.original.label ∧
      (lastL.label.OuterBarsSafe (fun x=>x≠degree) ↔lastR.label.OuterBarsSafe (fun x=>x≠degree)) := by
  subst ld;subst rd
  exact recent_normal_false_copy_first_safe_labels left right selected safe normalL normalR
    firstSafeL firstSafeR outL outR atL atR head

section
variable {initialSource source current : LTerm}
variable {prior ps F : List Path} {degree : Label} {n : Marked}
variable {leftStart rightStart : Path} {leftEdges rightEdges : List Path}
variable {labels : History ps source current}
variable {leftCut : ActualUnsafeMarkerCut F ps source current degree leftStart leftEdges}
variable {rightCut : ActualUnsafeMarkerCut F ps source current degree rightStart rightEdges}
variable {leftSnapshot : IncomingIncidenceSnapshot current leftCut.edge}
variable {rightSnapshot : IncomingIncidenceSnapshot current rightCut.edge}
variable {leftLeaf : DirectedMarkerLeafOutput F source degree leftCut.forward ps (leftCut.node.label.readLetters leftCut.forward)}
variable {rightLeaf : DirectedMarkerLeafOutput F source degree rightCut.forward ps (rightCut.node.label.readLetters rightCut.forward)}
variable {leftGeometry : SpineIncidenceProvenance F source degree leftCut.forward leftCut.spine leftCut.lookup leftLeaf leftSnapshot}
variable {rightGeometry : SpineIncidenceProvenance F source degree rightCut.forward rightCut.spine rightCut.lookup rightLeaf rightSnapshot}
variable (leftRecent : RecentSpineFrame leftGeometry) (rightRecent : RecentSpineFrame rightGeometry)

/-- Derived comparison indexed by the GIVEN geometries and recents. -/
structure GivenNormalFalseOriginalComparison
    (closed : Closed source.erase)
    (left : CanonicalAfterFarOutput labels leftCut leftSnapshot)
    (right : CanonicalAfterFarOutput labels rightCut rightSnapshot) where
  leftFalse : leftCut.forward=false
  rightFalse : rightCut.forward=false
  leftCompatibility : RecentFarCompatibility left leftRecent
  rightCompatibility : RecentFarCompatibility right rightRecent
  leftLow : ExpandedLastSelectedEndpoint leftRecent.packet.middle leftRecent.packet.site
    (leftRecent.packet.frame.edges.getLastD []) leftCut.forward (some leftCompatibility.expandedProper)
  rightLow : ExpandedLastSelectedEndpoint rightRecent.packet.middle rightRecent.packet.site
    (rightRecent.packet.frame.edges.getLastD []) rightCut.forward (some rightCompatibility.expandedProper)
  leftOriginal : ExpandedLastOriginalEndpoints F source leftRecent.packet.middle degree leftRecent.packet.event.labels
    (leftRecent.packet.frame.edges.getLastD []) leftLow.node leftCut.forward left.sourceProper leftCompatibility.originalEdges
  rightOriginal : ExpandedLastOriginalEndpoints F source rightRecent.packet.middle degree rightRecent.packet.event.labels
    (rightRecent.packet.frame.edges.getLastD []) rightLow.node rightCut.forward right.sourceProper rightCompatibility.originalEdges
  leftFirst : LTerm
  rightFirst : LTerm
  leftFirstLookup : leftRecent.packet.middle.subterm leftRecent.packet.first=some leftFirst
  rightFirstLookup : rightRecent.packet.middle.subterm rightRecent.packet.first=some rightFirst
  middleFirstEq : leftFirst.label=rightFirst.label
  middleLastEq : leftLow.node.label=rightLow.node.label
  lastSafety : leftLow.node.label.OuterBarsSafe (fun x=>x≠degree) ↔rightLow.node.label.OuterBarsSafe (fun x=>x≠degree)
  labelEq : leftOriginal.original.label=rightOriginal.original.label
  leftAux : AuxiliaryAt source leftOriginal.oldEdge
  rightAux : AuxiliaryAt source rightOriginal.oldEdge
  sourceIso : SuccessfulEndpointIso source closed (some leftOriginal.fromVertex) (some rightOriginal.fromVertex)
  targetIso : SuccessfulEndpointIso source closed (some leftOriginal.toVertex) (some rightOriginal.toVertex)

def GivenNormalFalseOriginalComparison.leftOutput
    {closed : Closed source.erase}
    {left : CanonicalAfterFarOutput labels leftCut leftSnapshot}
    {right : CanonicalAfterFarOutput labels rightCut rightSnapshot}
    (comparison : GivenNormalFalseOriginalComparison leftRecent rightRecent closed left right) :
    CanonicalRecentLastOutput labels leftCut leftSnapshot left :=
  ⟨leftLeaf,leftGeometry,leftRecent,comparison.leftCompatibility,comparison.leftLow,comparison.leftOriginal⟩

def GivenNormalFalseOriginalComparison.rightOutput
    {closed : Closed source.erase}
    {left : CanonicalAfterFarOutput labels leftCut leftSnapshot}
    {right : CanonicalAfterFarOutput labels rightCut rightSnapshot}
    (comparison : GivenNormalFalseOriginalComparison leftRecent rightRecent closed left right) :
    CanonicalRecentLastOutput labels rightCut rightSnapshot right :=
  ⟨rightLeaf,rightGeometry,rightRecent,comparison.rightCompatibility,comparison.rightLow,comparison.rightOriginal⟩

private theorem assemble_normal_comparison
    (sourceClosed : Closed source.erase)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (leftMore : leftCut.after≠[]) (rightMore : rightCut.after≠[])
    (normalL : ∃q : Path,q≠[] ∧leftRecent.packet.last=(leftRecent.packet.site++[.fn,.body])++q)
    (normalR : ∃q : Path,q≠[] ∧rightRecent.packet.last=(rightRecent.packet.site++[.fn,.body])++q)
    (firstSafeL : ∀node,leftRecent.packet.middle.subterm leftRecent.packet.first=some node →node.label.OuterBarsSafe (fun x=>x≠degree))
    (firstSafeR : ∀node,rightRecent.packet.middle.subterm rightRecent.packet.first=some node →node.label.OuterBarsSafe (fun x=>x≠degree))
    (left : CanonicalAfterFarOutput labels leftCut leftSnapshot)
    (right : CanonicalAfterFarOutput labels rightCut rightSnapshot)
    (good : CanonicalFarFullComparison sourceClosed left right)
    (head : leftCut.node.label=rightCut.node.label) :
    Nonempty (GivenNormalFalseOriginalComparison leftRecent rightRecent sourceClosed left right) := by
  have lFalse : leftCut.forward=false:=normal_direction leftRecent.packet.origin leftRecent.packet.reading normalL
  have rFalse : rightCut.forward=false:=normal_direction rightRecent.packet.origin rightRecent.packet.reading normalR
  obtain ⟨lCompat⟩:=Lamping.AG.RecentSpineFrame.canonical_far_compatibility leftRecent left
  obtain ⟨rCompat⟩:=Lamping.AG.RecentSpineFrame.canonical_far_compatibility rightRecent right
  obtain ⟨lLow,⟨lOut⟩⟩:=lCompat.expanded_last_endpoints selected sourceSafe
  obtain ⟨rLow,⟨rOut⟩⟩:=rCompat.expanded_last_endpoints selected sourceSafe
  obtain ⟨lFirst,rFirst,lAt,rAt,firstEq,lastEq,labelEq,safety⟩:=bool_normal_labels
    leftRecent rightRecent selected sourceSafe normalL normalR firstSafeL firstSafeR
    lOut rOut lLow.lookup rLow.lookup head lFalse rFalse
  have lSource :
      (lLow.node.label.OuterBarsSafe (fun x=>x≠degree) ∧lOut.fromVertex=left.sourceProper ∧lOut.sourceEdges=lCompat.originalEdges) ∨
      (¬lLow.node.label.OuterBarsSafe (fun x=>x≠degree) ∧SelectedOriginalSingleton F source degree lOut.fromVertex lOut.sourceEdges) := by
    simpa only [lFalse,Bool.false_eq_true,if_false] using lOut.sourceClass
  have rSource :
      (rLow.node.label.OuterBarsSafe (fun x=>x≠degree) ∧rOut.fromVertex=right.sourceProper ∧rOut.sourceEdges=rCompat.originalEdges) ∨
      (¬rLow.node.label.OuterBarsSafe (fun x=>x≠degree) ∧SelectedOriginalSingleton F source degree rOut.fromVertex rOut.sourceEdges) := by
    simpa only [rFalse,Bool.false_eq_true,if_false] using rOut.sourceClass
  have sourceIso : SuccessfulEndpointIso source sourceClosed (some lOut.fromVertex) (some rOut.fromVertex) := by
    rcases lSource with safeL | markedL
    · rcases rSource with safeR | markedR
      · refine ⟨lOut.sourceEdges,rOut.sourceEdges,lOut.sourceChain,rOut.sourceChain,?_⟩
        rw [safeL.2.2,safeR.2.2,lCompat.exactSourceEdges,rCompat.exactSourceEdges]
        exact good.2
      · exact False.elim (markedR.1 (safety.mp safeL.1))
    · rcases rSource with safeR | markedR
      · exact False.elim (markedL.1 (safety.mpr safeR.1))
      · exact selected_iso sourceClosed selected markedL.2 markedR.2 lOut.sourceChain rOut.sourceChain
  have targetIso : SuccessfulEndpointIso source sourceClosed (some lOut.toVertex) (some rOut.toVertex) := by
    have lt : SelectedOriginalSingleton F source degree lOut.toVertex lOut.targetEdges := by
      simpa only [lFalse,Bool.false_eq_true,if_false] using lOut.targetClass
    have rt : SelectedOriginalSingleton F source degree rOut.toVertex rOut.targetEdges := by
      simpa only [rFalse,Bool.false_eq_true,if_false] using rOut.targetClass
    exact selected_iso sourceClosed selected lt rt lOut.targetChain rOut.targetChain
  exact ⟨⟨lFalse,rFalse,lCompat,rCompat,lLow,rLow,lOut,rOut,lFirst,rFirst,lAt,rAt,firstEq,lastEq,safety,labelEq,
    normal_original_aux leftRecent leftMore normalL lOut,normal_original_aux rightRecent rightMore normalR rOut,
    sourceIso,targetIso⟩⟩

/-- Natural parent iso is used once; finite first-unsafe data uniqueness
aligns its outputs to the GIVEN cut/snapshot/geometry/recent. -/
theorem actual_given_normal_false_original_comparison
    (initial : INIT initialSource) (prefixHistory : History prior initialSource source)
    (sourceClosed : Closed source.erase)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) n)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (wholeIso : ChainIncidenceIso
      (chainSyntaxIncidence current (labels.closed sourceClosed) leftEdges)
      (chainSyntaxIncidence current (labels.closed sourceClosed) rightEdges))
    (leftMore : leftCut.after≠[])
    (normalL : ∃q : Path,q≠[] ∧leftRecent.packet.last=(leftRecent.packet.site++[.fn,.body])++q)
    (normalR : ∃q : Path,q≠[] ∧rightRecent.packet.last=(rightRecent.packet.site++[.fn,.body])++q)
    (leftFirstSafe : ∀node,leftRecent.packet.middle.subterm leftRecent.packet.first=some node →node.label.OuterBarsSafe (fun x=>x≠degree))
    (rightFirstSafe : ∀node,rightRecent.packet.middle.subterm rightRecent.packet.first=some node →node.label.OuterBarsSafe (fun x=>x≠degree)) :
    ∃left : CanonicalAfterFarOutput labels leftCut leftSnapshot,
      ∃right : CanonicalAfterFarOutput labels rightCut rightSnapshot,
        Nonempty (GivenNormalFalseOriginalComparison leftRecent rightRecent sourceClosed left right) := by
  have lFalse : leftCut.forward=false:=normal_direction leftRecent.packet.origin leftRecent.packet.reading normalL
  have rFalse : rightCut.forward=false:=normal_direction rightRecent.packet.origin rightRecent.packet.reading normalR
  have leftChain : PrerequisiteChain current leftStart leftEdges := by
    have actual:=leftCut.segment.close leftCut.remaining
    rw [←leftCut.split] at actual
    exact actual
  have rightChain : PrerequisiteChain current rightStart rightEdges := by
    have actual:=rightCut.segment.close rightCut.remaining
    rw [←rightCut.split] at actual
    exact actual
  rcases actual_parent_cuts_canonical_far_comparison initial prefixHistory sourceClosed old labels selected sourceSafe
    leftChain rightChain wholeIso with all | cut
  · have inside : leftCut.edge∈leftEdges :=
      Eq.mpr (congrArg (fun es : List Path=>leftCut.edge∈es) leftCut.split)
        (List.mem_append_right _ List.mem_cons_self)
    exact False.elim (cut_bad leftCut (all.1 _ inside))
  · obtain ⟨lc,rc,_length,_front,head,back,rest⟩:=cut
    have leq:=cut_unique leftCut lc leftMore lFalse
    cases leq
    obtain ⟨_rfront,_rhead,rtail⟩:=cut_lists rightCut rc
    have rightMore : rightCut.after≠[] := by
      intro empty
      have size:=congrArg List.length back
      simp only [List.length_map] at size
      rw [←rtail,empty,List.length_nil] at size
      exact leftMore (List.length_eq_zero_iff.mp size)
    have req:=cut_unique rightCut rc rightMore rFalse
    cases req
    rcases rest with empty | more
    · exact False.elim (leftMore empty.1)
    · obtain ⟨_lm,_rm,ls,rs,left,right,good⟩:=more
      have snapL:=ls.unique leftSnapshot
      have snapR:=rs.unique rightSnapshot
      cases snapL
      cases snapR
      have headEq : leftCut.node.label=rightCut.node.label := by
        simpa only [LTerm.labelAt,leftCut.lookup,rightCut.lookup,Option.map_some,Option.some.injEq] using head
      exact ⟨left,right,assemble_normal_comparison leftRecent rightRecent sourceClosed selected sourceSafe
        leftMore rightMore normalL normalR leftFirstSafe rightFirstSafe left right good headEq⟩

theorem GivenNormalFalseOriginalComparison.source_fragments
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    {closed : Closed source.erase}
    {left : CanonicalAfterFarOutput labels leftCut leftSnapshot}
    {right : CanonicalAfterFarOutput labels rightCut rightSnapshot}
    (comparison : GivenNormalFalseOriginalComparison leftRecent rightRecent closed left right)
    (selection : OccurrenceFragmentSelection source g root)
    (auxiliary : AuxiliarySeparation closed selection) :
    (selection comparison.leftOutput.originalEdge).fragment.segments=
      (selection comparison.rightOutput.originalEdge).fragment.segments := by
  classical
  apply Classical.byContradiction
  intro different
  have labelEq : SyntaxIncidence.label source comparison.leftOutput.originalEdge=
      SyntaxIncidence.label source comparison.rightOutput.originalEdge := by
    rw [SyntaxIncidence.label_of_lookup source _ comparison.leftOriginal.lookup,
      SyntaxIncidence.label_of_lookup source _ comparison.rightOriginal.lookup]
    exact comparison.labelEq
  apply auxiliary comparison.leftOutput.originalEdge comparison.rightOutput.originalEdge
    comparison.leftAux comparison.rightAux labelEq different
  constructor
  · rw [SyntaxIncidence.source_eq_of_spec source _ comparison.leftOriginal.sourceSpec,
      SyntaxIncidence.source_eq_of_spec source _ comparison.rightOriginal.sourceSpec]
    exact comparison.sourceIso
  · rw [SyntaxIncidence.target_eq_of_spec source closed _ comparison.leftOriginal.targetSpec,
      SyntaxIncidence.target_eq_of_spec source closed _ comparison.rightOriginal.targetSpec]
    exact comparison.targetIso
end
#print axioms actual_given_normal_false_original_comparison
#print axioms GivenNormalFalseOriginalComparison.source_fragments
end Lamping.AG
