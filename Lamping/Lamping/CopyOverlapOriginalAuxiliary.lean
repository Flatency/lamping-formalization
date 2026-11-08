import Lamping.Lamping.ExpandedLastEndpointChains
import Lamping.Lambda.AuxiliaryNodeHistoryOrigins
namespace Lamping.Lambda.Labelled
open SyntaxIncidence
variable {source target : LTerm}
private theorem root_copy_shape
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (firstEq : first=site++[.arg]) (lastEq : last=site++[.fn,.body]) :
    edge=site ∧reader=edge := by
  cases origin with
  | resultFunction => have n:=congrArg List.length firstEq;simp at n
  | resultLambda => have n:=congrArg List.length firstEq;simp at n
  | copyFunction => have n:=congrArg List.length lastEq;simp at n
  | copyLambda occurs copy reading oldLambda =>
    have nil : _=[]:=List.append_cancel_left (by simpa only [List.append_nil] using lastEq)
    exact ⟨by simpa only [nil,List.append_nil] using copy,reading⟩
private theorem root_copy_direction
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected t reader edge forward)
    (firstEq : first=site++[.arg]) (lastEq : last=site++[.fn,.body]) : forward=false := by
  obtain ⟨_,same⟩:=root_copy_shape origin firstEq lastEq
  cases forward with
  | false => rfl
  | true => have n:=congrArg List.length (same.trans reading.2);simp at n
private theorem root_copy_end
    (expansion : CreatedReadingExpansion body site first last forward es ds)
    (firstEq : first=site++[.arg]) (lastEq : last=site++[.fn,.body]) : es.getLastD []=site := by
  cases expansion with
  | resultFunction => have n:=congrArg List.length firstEq;simp at n
  | resultOverlap => have n:=congrArg List.length firstEq;simp at n
  | copyFunction => have n:=congrArg List.length lastEq;simp at n
  | resultLambda => have n:=congrArg List.length firstEq;simp at n
  | copyLambda nonroot =>
    have nil : _=[]:=List.append_cancel_left (by simpa only [List.append_nil] using lastEq)
    exact False.elim (nonroot nil)
  | copyOverlap => rfl
private theorem uncreated_last
    {labels : History ps source target}
    (trace : UncreatedNodeHistoryPreimage labels edge old) : edge.getLast?=old.getLast? := by
  induction trace with
  | nil => rfl
  | one redex origin uncreated tail ih => exact ih.trans (origin.uncreated_last_step uncreated)
end Lamping.Lambda.Labelled
namespace Lamping.AG
open Graph Lambda Lambda.Labelled SyntaxIncidence
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
section
variable {source current : LTerm} {F ps : List Path} {degree : Label}
variable {start : Path} {edges : List Path}
variable {cut : ActualUnsafeMarkerCut F ps source current degree start edges}
variable {snapshot : IncomingIncidenceSnapshot current cut.edge}
variable {leaf : DirectedMarkerLeafOutput F source degree cut.forward ps (cut.node.label.readLetters cut.forward)}
variable {geometry : SpineIncidenceProvenance F source degree cut.forward cut.spine cut.lookup leaf snapshot}
/-- The actual nonterminal root-copy expansion ends at the selected APP.
Its original incoming edge is auxiliary; its target has the exact selected singleton. -/
theorem ActualUnsafeMarkerCut.copy_overlap_original_last_auxiliary
    (recent : RecentSpineFrame geometry) (more : cut.after≠[])
    (rootCopy : recent.packet.first=recent.packet.site++[Step.arg] ∧
      recent.packet.last=recent.packet.site++[Step.fn,Step.body])
    (selected : ∀name∈F,source.degreeAt name=some degree)
    {lastNode : LTerm} {originalFar : ProperPosition source} {farEdges : List Path}
    (out : ExpandedLastOriginalEndpoints F source recent.packet.middle degree recent.packet.event.labels
      (recent.packet.frame.edges.getLastD []) lastNode cut.forward originalFar farEdges) :
    cut.forward=false ∧recent.packet.frame.edges.getLastD []=recent.packet.site ∧
    AuxiliaryAt source out.oldEdge ∧
    ∃name beta body argument,name∈F ∧
      source.subterm name=some (.app beta (.lam degree body) argument) ∧
      out.toVertex.val=name ∧out.targetEdges=[name++[Step.fn]] := by
  have direction:=root_copy_direction recent.packet.origin recent.packet.reading rootCopy.1 rootCopy.2
  have endEq:=root_copy_end recent.packet.frame.expansion rootCopy.1 rootCopy.2
  obtain ⟨edgeEq,_⟩:=root_copy_shape recent.packet.origin rootCopy.1 rootCopy.2
  have notFn : cut.edge.getLast?≠some .fn := by
    intro fn
    have pos:cut.forward=true:=(cut.reading.nonredex_forward_iff_function
      (nonterminal_not_redex cut.remaining more)).mpr fn
    rw [direction] at pos;cases pos
  have siteNotFn : recent.packet.site.getLast?≠some .fn := by
    rw [←edgeEq,←uncreated_last recent.uncreatedSuffix];exact notFn
  have middleAux : AuxiliaryAt recent.packet.middle recent.packet.site := by
    constructor
    · rintro ⟨parent,a,fn,arg,split,_⟩
      exact siteNotFn (by rw [split,List.getLast?_concat])
    · rintro ⟨a,b,atLambda⟩
      rw [recent.packet.event.redex] at atLambda;cases atLambda
  have actualAux : AuxiliaryAt recent.packet.middle (recent.packet.frame.edges.getLastD []):=by rw [endEq];exact middleAux
  have actualLookup := recent.packet.event.redex
  have aux : AuxiliaryAt source out.oldEdge := by
    exact (out.nodeTrace.auxiliary_source (by rw [endEq];exact actualLookup) actualAux).choose_spec.2
  obtain ⟨name,member,⟨beta,alpha,body,argument,redex⟩,appTrace,_⟩:=
    recent.packet.event.beforeOld.selected_app_function_preimages recent.packet.event.labels recent.packet.event.member
  have degreeEq:=selected name member
  simp only [LTerm.degreeAt,redex,Option.bind_some,LTerm.degree] at degreeEq
  have same:=Option.some.inj degreeEq
  subst alpha
  let app : ProperPosition recent.packet.middle:=⟨recent.packet.site,Or.inl ⟨_,_,_,actualLookup⟩⟩
  let oldApp : ProperPosition source:=⟨name,Or.inl ⟨beta,.lam degree body,argument,redex⟩⟩
  obtain ⟨v,atV,trace⟩:=out.targetAncestry
  have appTarget : Target recent.packet.middle (recent.packet.frame.edges.getLastD []) (some app):=by rw [endEq];exact Or.inl rfl
  have vEq:=Target.unique atV appTarget
  have appOrigin : BetaVertexHistoryPreimage recent.packet.event.labels (some app) (some oldApp):=.proper appTrace
  have vertexEq:= (vEq ▸ trace).unique appOrigin
  have position : out.toVertex.val=name:=congrArg Subtype.val (Option.some.inj vertexEq)
  have chain : PrerequisiteChain source name out.targetEdges:=by
    have c:=out.targetChain
    change PrerequisiteChain source out.toVertex.val out.targetEdges at c
    rw [position] at c;exact c
  exact ⟨direction,endEq,aux,name,beta,body,argument,member,redex,position,chain.unique (.redex_app redex)⟩
end
end Lamping.AG
