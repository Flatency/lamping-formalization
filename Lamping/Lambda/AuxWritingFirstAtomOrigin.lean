import Lamping.Lamping.NonterminalFarBoundary
namespace Lamping.Lambda.Labelled
open SyntaxIncidence InteriorSourceBlock NonterminalFarBoundary

private theorem proper_parent_origin
    {ps : List Path} {source current : LTerm}
    (labels : History ps source current) (parent : ProperPosition current) :
    ∃oldParent : ProperPosition source,
      BetaNodeHistoryPreimage labels parent.val oldParent.val := by
  rcases parent.property with ⟨a,fn,arg,lookup⟩ |⟨a,body,lookup⟩
  · obtain ⟨position,node,atOld,trace⟩:=labels.node_preimage_from_lookup lookup
    obtain ⟨ancestor,atAncestor,last,tag⟩:=trace.lastAtom_constructor lookup
    cases ancestor with
    | var => cases tag
    | lam => cases tag
    | app stamp f x => exact ⟨⟨position,Or.inl ⟨stamp,f,x,atAncestor⟩⟩,trace⟩
  · obtain ⟨position,node,atOld,trace⟩:=labels.node_preimage_from_lookup lookup
    obtain ⟨ancestor,atAncestor,last,tag⟩:=trace.lastAtom_constructor lookup
    cases ancestor with
    | var => cases tag
    | app => cases tag
    | lam stamp b => exact ⟨⟨position,Or.inr ⟨stamp,b,atAncestor⟩⟩,trace⟩

/-- A literal writing-FIRST atom retains the real current parent ancestry.
Its arrival is the selected APP or the selected lambda's actual bound VAR. -/
theorem aux_writing_first_atom_origin
    {source current localTarget currentNode localNode : LTerm}
    {F ps : List Path} {marked : Marked} {edge : Path}
    {atom : Nat} {kind : Bool} {payload : Label} {tail : List Letter}
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) marked)
    (labels : History ps source current)
    (localHistory : History ps (initLabels source.erase) localTarget)
    (lookup : current.subterm edge=some currentNode)
    (aux : AuxiliaryAt current edge)
    (localLookup : localTarget.subterm edge=some localNode)
    (window : localNode.label.letters=[.atom atom,bar kind payload]++tail)
    (currentParent : ProperPosition current)
    (sourceSpec : Source current edge (some currentParent)) :
    ∃oldParent : ProperPosition source,
      BetaVertexHistoryPreimage labels (some currentParent) (some oldParent) ∧
      ∃position env ctx basisNode,
        SourceSubterm [] .external (initLabels source.erase) position env ctx basisNode ∧
        basisNode.label=Label.atom atom ∧
        source.subterm position=some (basisNode.relabel (initialRelabelling source 0)) ∧
        AuxiliaryAt source position ∧
        ∃selected : SelectedRedex source F,
          Source source position (some oldParent) ∧
          Target source position (some (selected.vertex (!kind))) := by
  obtain ⟨oldParent,parentTrace⟩:=proper_parent_origin labels currentParent
  obtain ⟨routeCtx,finish,route⟩:=actual_old_node_route old localHistory localLookup
  have boundary : localNode.label.readLetters false=tail.reverse++[bar kind payload,.atom atom] := by
    simp only [Label.readLetters,Bool.false_eq_true,ite_false,window,
      List.reverse_cons,List.nil_append,List.cons_append,List.append_assoc]
  obtain ⟨geometry⟩:=selected_route_far_boundary (init_is_INIT _) route boundary
  obtain ⟨position,env,ctx,node,occurrence,edgeEq⟩:=edge_occurrence geometry.member
  have ports : geometry.edge.fromPort=routeCtx ∧geometry.edge.toPort=geometry.selected.beforePort kind := geometry.ports
  have contextEq : ctx=routeCtx :=
    (source_edge_departure env ctx node).symm.trans ((congrArg SourceEdge.fromPort edgeEq).trans ports.1)
  have arrival:=occurrence_before_marker (init_is_INIT _) occurrence geometry.selected
    ((congrArg SourceEdge.toPort edgeEq).trans ports.2)
  have atomic : node.label=Label.atom atom :=
    (source_edge_label env ctx node).symm.trans ((congrArg SourceEdge.atom edgeEq).trans geometry.atomic)
  have globalLookup : source.subterm position=some (node.relabel (initialRelabelling source 0)) := by
    have factor : (initLabels source.erase).relabel (initialRelabelling source 0)=source := initialRelabelling_factor source 0
    simpa only [factor] using lookup_relabel occurrence.lookup (initialRelabelling source 0)
  let redex : SelectedRedex source F:=global_redex geometry.selected
  have role:=original_incoming_role localHistory localLookup route.forget occurrence contextEq
  have oldSource : Source source position (some oldParent) := by
    obtain ⟨step,parentTerm,parentPort,split,parentLookup,departure⟩:=sourceSpec
    have sameErase:=SpineReannotation.history_erase labels localHistory (erase_initLabels source.erase).symm
    obtain ⟨localParent,localParentLookup,erased⟩:=SpineReannotation.paired_lookup sameErase parentLookup
    cases departure with
    | fn => exact False.elim (aux.1 ⟨currentParent.val,_,_,_,split,parentLookup⟩)
    | arg =>
      cases localParent with
      | var => cases erased
      | lam => cases erased
      | app stamp fn arg =>
        exact arg_far_source labels localHistory (actual_old_routes old localHistory) localParentLookup
          (by rw [←split];exact localLookup) route.forget occurrence contextEq oldParent parentTrace
    | body =>
      cases localParent with
      | var => cases erased
      | app => cases erased
      | lam stamp body =>
        exact body_far_source labels localHistory (actual_old_routes old localHistory) localParentLookup
          (by rw [←split];exact localLookup) route.forget occurrence contextEq oldParent parentTrace
  have notFunction : ¬∃parent a fn arg,position=parent++[Step.fn] ∧source.subterm parent=some (.app a fn arg) := by
    rintro ⟨parent,a,fn,arg,split,atParent⟩
    have last : edge.getLast?=some .fn := by rw [←role,split];simp
    obtain ⟨currentEnv,currentCtx,currentOccurrence⟩:=SourceSubterm.of_lookup current lookup [] .external
    rcases currentOccurrence.last_departure with ⟨root,_⟩ |⟨actualParent,step,child,atChild,atActualParent,departure⟩
    · rw [root] at last;cases last
    · have sameStep : step=Step.fn := by simpa only [atChild,List.getLast?_concat,Option.some.injEq] using last
      subst step
      cases departure with
      | fn => exact aux.1 ⟨actualParent,_,_,_,atChild,atActualParent⟩
  have targetSpec : Target source position (some (redex.vertex (!kind))) := by
    cases kind with
    | true => exact Or.inl arrival
    | false =>
      obtain ⟨stamp,index,rest,nodeEq,split,depth⟩:=arrival
      exact Or.inr ⟨stamp.relabel (initialRelabelling source 0),index,redex.degree,redex.body,rest,
        by simpa only [nodeEq,LTerm.relabel] using globalLookup,redex.function_lookup,split,depth⟩
  have notLambda : ¬∃stamp body,source.subterm position=some (.lam stamp body) := by
    rintro ⟨stamp,body,atLambda⟩
    cases kind with
    | true =>
      change position=redex.position at arrival
      have selectedLookup:=redex.lookup
      rw [←arrival] at selectedLookup
      rw [selectedLookup] at atLambda
      cases atLambda
    | false =>
      obtain ⟨a,index,rest,nodeEq,split,depth⟩:=arrival
      rw [nodeEq] at globalLookup
      simp only [LTerm.relabel] at globalLookup
      rw [globalLookup] at atLambda
      cases atLambda
  exact ⟨oldParent,.proper parentTrace,position,env,ctx,node,occurrence,atomic,globalLookup,
    ⟨notFunction,notLambda⟩,redex,oldSource,targetSpec⟩
end Lamping.Lambda.Labelled
#print axioms Lamping.Lambda.Labelled.aux_writing_first_atom_origin
