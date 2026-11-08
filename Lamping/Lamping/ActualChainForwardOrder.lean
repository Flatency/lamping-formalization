import Lamping.Lamping.ActualChainIncidenceOrder
import Lamping.Lambda.ActualNodeLabelAncestry
import Lamping.Lambda.ActualIncomingLabelRoles
namespace Lamping.Lambda.Labelled

private theorem redex_of_function_lambda
    (lookup : current.subterm edge=some (.lam stamp body))
    (function : edge.getLast?=some .fn) : PrerequisiteRedexEdge current edge := by
  obtain ⟨parent,equal⟩ := List.getLast?_eq_some_iff.mp function
  subst edge
  rw [LTerm.subterm_append] at lookup
  cases actual : current.subterm parent with
  | none => rw [actual] at lookup;cases lookup
  | some node =>
    rw [actual] at lookup
    cases node with
    | var => cases lookup
    | lam => cases lookup
    | app appStamp fn arg =>
      have equal : fn=.lam stamp body := Option.some.inj (by simpa only [Option.bind_some,LTerm.subterm] using lookup)
      subst fn
      exact ⟨parent,appStamp,stamp,body,arg,rfl,actual⟩

/-- Same current labels retain both actual constructor and incoming role,
which identifies redex-edge status without identifying current positions. -/
theorem History.redex_edge_of_equal_label
    {ps : List Path} {source current left right : LTerm} {p q : Path}
    (labels : History ps source current) (initial : INIT source)
    (atLeft : current.subterm p=some left) (atRight : current.subterm q=some right)
    (same : left.label=right.label) (redex : PrerequisiteRedexEdge current p) :
    PrerequisiteRedexEdge current q := by
  obtain ⟨parent,a,l,body,arg,equal,atParent⟩ := redex
  have child : current.subterm p=some (.lam l body) := by rw [equal,LTerm.subterm_append,atParent];rfl
  have leftEq := Option.some.inj (atLeft.symm.trans child)
  subst left
  have tag:=labels.node_constructor_eq_of_label initial atLeft atRight same
  have role:=labels.incoming_role_eq_of_label initial atLeft atRight same
  have rightFunction : q.getLast?=some .fn := by rw [←role,equal];simp
  cases right with
  | var => cases tag
  | app => cases tag
  | lam stamp inner => exact redex_of_function_lambda atRight rightFunction
end Lamping.Lambda.Labelled
namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem redex_slot_last (chain : PrerequisiteChain t start edges)
    (k : Fin edges.length) (redex : PrerequisiteRedexEdge t (edges.get k)) :
    k.val=edges.length-1 := by
  obtain ⟨before,last,equal,_,old⟩ := chain.redex_only_last
  have member : edges.get k∈before++[last] := equal ▸ List.get_mem edges k
  rw [List.mem_append] at member
  have edgeEq : edges.get k=last := by
    rcases member with below | final
    · exact False.elim (old _ below redex)
    · exact List.mem_singleton.mp final
  have positive : 0<edges.length := List.length_pos_iff.mpr chain.nonempty
  have lastEq : edges.get ⟨edges.length-1,by omega⟩=last := by
    simp only [equal,List.length_append,List.length_singleton,Nat.add_sub_cancel,List.get_eq_getElem]
    simp
  have same : edges[k.val]?=edges[edges.length-1]? := by
    simp only [List.getElem?_eq_getElem k.isLt,List.getElem?_eq_getElem (by omega : edges.length-1<edges.length)]
    exact congrArg some (edgeEq.trans lastEq.symm)
  exact List.getElem?_inj k.isLt chain.nodup same

private theorem selected_redex_preserved
    {ps : List Path} {source current : LTerm} {es fs : List Path}
    {closed : Closed current.erase}
    (labels : History ps source current) (initial : INIT source)
    (iso : ChainIncidenceIso (chainSyntaxIncidence current closed es) (chainSyntaxIncidence current closed fs))
    (edge : (chainSyntaxIncidence current closed es).Edge)
    (redex : PrerequisiteRedexEdge current edge.val.val) :
    PrerequisiteRedexEdge current (iso.edges edge).val.val := by
  obtain ⟨left,leftLookup⟩ := SyntaxIncidence.edge_lookup current edge.val
  obtain ⟨right,rightLookup⟩ := SyntaxIncidence.edge_lookup current (iso.edges edge).val
  have equal:=iso.label_eq edge
  change SyntaxIncidence.label current edge.val=SyntaxIncidence.label current (iso.edges edge).val at equal
  rw [SyntaxIncidence.label_of_lookup current edge.val leftLookup,
    SyntaxIncidence.label_of_lookup current (iso.edges edge).val rightLookup] at equal
  exact labels.redex_edge_of_equal_label initial leftLookup rightLookup equal redex

/-- A same-INIT actual full history anchors the only redex edge at the
terminal slot, sharpening the general order/reverse alternative to forward. -/
theorem actual_chain_incidence_slot_forward
    {ps : List Path} {source current : LTerm} {leftStart rightStart : Path} {es fs : List Path}
    (labels : History ps source current) (initial : INIT source) (closed : Closed current.erase)
    (leftChain : PrerequisiteChain current leftStart es) (rightChain : PrerequisiteChain current rightStart fs)
    (iso : ChainIncidenceIso (chainSyntaxIncidence current closed es) (chainSyntaxIncidence current closed fs)) :
    let first:=actual_chain_incidence_presentation closed leftChain
    let second:=actual_chain_incidence_presentation closed rightChain
    es.length=fs.length ∧∀k,(second.presentation.edges.invFun (iso.edges (first.presentation.edges k))).val=k.val := by
  dsimp only
  let first:=actual_chain_incidence_presentation closed leftChain
  let second:=actual_chain_incidence_presentation closed rightChain
  obtain ⟨length,up | down⟩:=actual_chain_incidence_slot_order_or_reverse closed closed leftChain rightChain iso
  · exact ⟨length,up⟩
  · have positive : 0<es.length := List.length_pos_iff.mpr leftChain.nonempty
    let final : Fin es.length := ⟨es.length-1,by omega⟩
    have lastRedex : PrerequisiteRedexEdge current (es.get final) := by
      obtain ⟨edge,atLast,redex⟩ := leftChain.last_redex
      have same:=List.getLast_of_getLast?_eq_some atLast
      have value : es.get final=edge := by simpa only [List.getLast_eq_getElem,List.get_eq_getElem] using same
      exact value ▸ redex
    have redex : PrerequisiteRedexEdge current (first.presentation.edges final).val.val :=
      (first.edge_at final) ▸ lastRedex
    have mappedRedex:=selected_redex_preserved labels initial iso (first.presentation.edges final) redex
    let mapped:=second.presentation.edges.invFun (iso.edges (first.presentation.edges final))
    have mappedEq : (iso.edges (first.presentation.edges final)).val.val=fs.get mapped := by
      rw [←second.presentation.edges.right_inv (iso.edges (first.presentation.edges final))]
      exact second.edge_at mapped
    have lastIndex:=redex_slot_last rightChain mapped (mappedEq ▸ mappedRedex)
    have anchor : (second.presentation.edges.invFun (iso.edges (first.presentation.edges final))).val=fs.length-1 := lastIndex
    have reverseLast : (second.presentation.edges.invFun (iso.edges (first.presentation.edges final))).val=fs.length-1-(es.length-1) := by
      simpa only [final] using down final
    have one : es.length=1 := by omega
    refine ⟨length,?_⟩
    intro k
    have bound:=k.isLt
    have zero : k.val=0 := by omega
    have answer:=down k
    omega

/-- The actual bare iso maps the literal successful-chain edge list in
forward order. No distinguished start or direction is added to the iso. -/
theorem actual_chain_incidence_forward
    {ps : List Path} {source current : LTerm} {leftStart rightStart : Path} {es fs : List Path}
    (labels : History ps source current) (initial : INIT source) (closed : Closed current.erase)
    (leftChain : PrerequisiteChain current leftStart es) (rightChain : PrerequisiteChain current rightStart fs)
    (iso : ChainIncidenceIso (chainSyntaxIncidence current closed es) (chainSyntaxIncidence current closed fs)) :
    es.length=fs.length ∧actualChainIsoImage closed closed leftChain rightChain iso=fs := by
  let first:=actual_chain_incidence_presentation closed leftChain
  let second:=actual_chain_incidence_presentation closed rightChain
  obtain ⟨length,forward⟩:=actual_chain_incidence_slot_forward labels initial closed leftChain rightChain iso
  refine ⟨length,?_⟩
  apply List.ext_getElem (by simp only [actualChainIsoImage,List.length_ofFn];exact length)
  intro i hi hj
  have bound : i<es.length := by simpa only [actualChainIsoImage,List.length_ofFn] using hi
  let k : Fin es.length := ⟨i,bound⟩
  have index : second.presentation.edges.invFun (iso.edges (first.presentation.edges k))=⟨i,hj⟩ :=
    Fin.ext (forward k)
  have equal:=congrArg second.presentation.edges index
  rw [second.presentation.edges.right_inv] at equal
  simp only [actualChainIsoImage,List.getElem_ofFn]
  exact (congrArg (fun e=>(e.val.val : Path)) equal).trans (second.edge_at ⟨i,hj⟩)

/-- Same original INIT/history fixes the complete READ label sequence in
forward edge order. It does not assert that terminal read signs agree. -/
theorem actual_chain_labels_forward
    {ps : List Path} {source current : LTerm} {leftStart rightStart : Path} {es fs : List Path}
    (labels : History ps source current) (initial : INIT source) (closed : Closed current.erase)
    (leftChain : PrerequisiteChain current leftStart es) (rightChain : PrerequisiteChain current rightStart fs)
    (iso : ChainIncidenceIso (chainSyntaxIncidence current closed es) (chainSyntaxIncidence current closed fs)) :
    es.map current.labelAt=fs.map current.labelAt := by
  have imageLabels:=actual_chain_image_labels closed closed leftChain rightChain iso
  rw [(actual_chain_incidence_forward labels initial closed leftChain rightChain iso).2] at imageLabels
  exact imageLabels.symm
end Lamping.AG
