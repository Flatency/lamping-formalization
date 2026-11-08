import Lamping.Lamping.ActualChainPathPresentations
namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem ofFn_nodup {A : Type} {n : Nat} {f : Fin n →A} (injective : Function.Injective f) :
    (List.ofFn f).Nodup := by
  rw [List.nodup_iff_pairwise_ne,List.pairwise_iff_getElem]
  intro i j hi hj less equal
  simp only [List.getElem_ofFn] at equal
  have same : i=j := by simpa using congrArg Fin.val (injective equal)
  omega

theorem finite_bij_length_eq (bijection : Bij (Fin n) (Fin m)) : n=m := by
  classical
  have leftNodup:=ofFn_nodup bijection.injective
  have rightNodup:=ofFn_nodup (f:=fun x : Fin m=>x) (fun _ _ h=>h)
  have perm : List.Perm (List.ofFn bijection.toFun) (List.ofFn (fun x : Fin m=>x)) := by
    apply List.perm_iff_count.mpr
    intro value
    rw [leftNodup.count,rightNodup.count]
    have leftMem : value∈List.ofFn bijection.toFun := List.mem_ofFn.mpr ⟨bijection.invFun value,bijection.right_inv value⟩
    have rightMem : value∈List.ofFn (fun x : Fin m=>x) := List.mem_ofFn.mpr ⟨value,rfl⟩
    simp only [leftMem,rightMem,if_true]
  simpa only [List.length_ofFn] using perm.length_eq

theorem actual_chain_incidence_length_eq
    {left right : LTerm} {leftStart rightStart : Path} {es fs : List Path}
    (leftClosed : Closed left.erase) (rightClosed : Closed right.erase)
    (leftChain : PrerequisiteChain left leftStart es) (rightChain : PrerequisiteChain right rightStart fs)
    (iso : ChainIncidenceIso (chainSyntaxIncidence left leftClosed es) (chainSyntaxIncidence right rightClosed fs)) :
    es.length=fs.length := by
  let first := actual_chain_incidence_presentation leftClosed leftChain
  let second := actual_chain_incidence_presentation rightClosed rightChain
  exact finite_bij_length_eq (first.presentation.edges.trans (iso.edges.trans second.presentation.edges.symm))

private theorem matched_edge_slots
    {left right : EdgeLabelledIncidence} {n : Nat}
    (first : IndexedSimpleIncidencePath left n) (second : IndexedSimpleIncidencePath right n)
    (iso : ChainIncidenceIso left right) (k : Fin n) :
    let j := second.edges.invFun (iso.edges (first.edges k))
    ((first.mappedSlot second iso ⟨k.val,by omega⟩).val=j.val ∧
      (first.mappedSlot second iso ⟨k.val+1,by omega⟩).val=j.val+1) ∨
    ((first.mappedSlot second iso ⟨k.val,by omega⟩).val=j.val+1 ∧
      (first.mappedSlot second iso ⟨k.val+1,by omega⟩).val=j.val) := by
  let j := second.edges.invFun (iso.edges (first.edges k))
  have edgeEq : second.edges j=iso.edges (first.edges k) := second.edges.right_inv _
  have identify (a b : Fin (n+1)) (equal : iso.vertices (first.vertices a)=second.vertices b) :
      (first.mappedSlot second iso a).val=b.val := by
    have mapped:=congrArg second.vertices.invFun equal
    have equal : first.mappedSlot second iso a=b := by
      simpa only [IndexedSimpleIncidencePath.mappedSlot,second.vertices.left_inv] using mapped
    exact congrArg Fin.val equal
  have rightInc:=second.incidence j
  rw [edgeEq] at rightInc
  rcases first.incidence k with ⟨ls,lt⟩ | ⟨lt,ls⟩
  · have source:= (congrArg iso.vertices ls).symm.trans (iso.source_eq _)
    have target:= (congrArg iso.vertices lt).symm.trans (iso.target_eq _)
    rcases rightInc with ⟨rs,rt⟩ | ⟨rt,rs⟩
    · exact Or.inl ⟨identify _ _ (source.trans rs),identify _ _ (target.trans rt)⟩
    · exact Or.inr ⟨identify _ _ (source.trans rs),identify _ _ (target.trans rt)⟩
  · have target:= (congrArg iso.vertices lt).symm.trans (iso.target_eq _)
    have source:= (congrArg iso.vertices ls).symm.trans (iso.source_eq _)
    rcases rightInc with ⟨rs,rt⟩ | ⟨rt,rs⟩
    · exact Or.inr ⟨identify _ _ (target.trans rt),identify _ _ (source.trans rs)⟩
    · exact Or.inl ⟨identify _ _ (target.trans rt),identify _ _ (source.trans rs)⟩

theorem IndexedSimpleIncidencePath.edge_order_or_reverse
    {left right : EdgeLabelledIncidence} {n : Nat}
    (first : IndexedSimpleIncidencePath left n) (second : IndexedSimpleIncidencePath right n)
    (iso : ChainIncidenceIso left right) :
    (∀k,(second.edges.invFun (iso.edges (first.edges k))).val=k.val) ∨
    (∀k,(second.edges.invFun (iso.edges (first.edges k))).val=n-1-k.val) := by
  rcases first.iso_order_or_reverse second iso with up | down
  · apply Or.inl
    intro k
    have a:=up ⟨k.val,by omega⟩
    have b:=up ⟨k.val+1,by omega⟩
    rcases matched_edge_slots first second iso k with ⟨left,right⟩ | ⟨left,right⟩ <;>
      dsimp only at a b left right <;> omega
  · apply Or.inr
    intro k
    have a:=down ⟨k.val,by omega⟩
    have b:=down ⟨k.val+1,by omega⟩
    rcases matched_edge_slots first second iso k with ⟨left,right⟩ | ⟨left,right⟩
    · dsimp only at a b left right
      omega
    · dsimp only at a b left right
      have bound:=k.isLt;omega

theorem IndexedSimpleIncidencePath.edge_lists_order_or_reverse
    {left right : EdgeLabelledIncidence} {n m : Nat} {A : Type}
    (first : IndexedSimpleIncidencePath left n) (second : IndexedSimpleIncidencePath right m)
    (iso : ChainIncidenceIso left right) (project : right.Edge →A) (length : n=m) :
    List.ofFn (fun k=>project (iso.edges (first.edges k)))=List.ofFn (fun k=>project (second.edges k)) ∨
    List.ofFn (fun k=>project (iso.edges (first.edges k)))=(List.ofFn (fun k=>project (second.edges k))).reverse := by
  subst m
  rcases first.edge_order_or_reverse second iso with up | down
  · apply Or.inl
    apply List.ext_getElem (by simp only [List.length_ofFn])
    intro i hi hj
    simp only [List.getElem_ofFn]
    have index : second.edges.invFun (iso.edges (first.edges ⟨i,by simpa using hi⟩))=⟨i,by simpa using hj⟩ :=
      Fin.ext (up _)
    have equal:=congrArg second.edges index
    rw [second.edges.right_inv] at equal
    exact congrArg project equal
  · apply Or.inr
    apply List.ext_getElem (by simp only [List.length_ofFn,List.length_reverse])
    intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_reverse,List.length_ofFn]
    have index : second.edges.invFun (iso.edges (first.edges ⟨i,by simpa using hi⟩))=
        ⟨n-1-i,by simp only [List.length_reverse,List.length_ofFn] at hj;omega⟩ := Fin.ext (down _)
    have equal:=congrArg second.edges index
    rw [second.edges.right_inv] at equal
    exact congrArg project equal

noncomputable def actualChainIsoImage
    {left right : LTerm} {leftStart rightStart : Path} {es fs : List Path}
    (leftClosed : Closed left.erase) (rightClosed : Closed right.erase)
    (leftChain : PrerequisiteChain left leftStart es) (_rightChain : PrerequisiteChain right rightStart fs)
    (iso : ChainIncidenceIso (chainSyntaxIncidence left leftClosed es) (chainSyntaxIncidence right rightClosed fs)) : List Path :=
  List.ofFn (fun k=>(iso.edges ((actual_chain_incidence_presentation leftClosed leftChain).presentation.edges k)).val.val)

private theorem actual_edge_enum
    {term : LTerm} {closed : Closed term.erase} {start : Path} {edges : List Path}
    {chain : PrerequisiteChain term start edges} (actual : ActualChainPathPresentation closed chain) :
    List.ofFn (fun k=>(actual.presentation.edges k).val.val)=edges := by
  apply List.ext_getElem (by simp only [List.length_ofFn])
  intro i hi hj
  simp only [List.getElem_ofFn]
  exact actual.edge_at ⟨i,hj⟩

/-- Actual successful chains provide their own lengths and complete path
presentations. The mapped literal edge list is in the original order or reverse. -/
theorem actual_chain_incidence_order_or_reverse
    {left right : LTerm} {leftStart rightStart : Path} {es fs : List Path}
    (leftClosed : Closed left.erase) (rightClosed : Closed right.erase)
    (leftChain : PrerequisiteChain left leftStart es) (rightChain : PrerequisiteChain right rightStart fs)
    (iso : ChainIncidenceIso (chainSyntaxIncidence left leftClosed es) (chainSyntaxIncidence right rightClosed fs)) :
    es.length=fs.length ∧
    (actualChainIsoImage leftClosed rightClosed leftChain rightChain iso=fs ∨
      actualChainIsoImage leftClosed rightClosed leftChain rightChain iso=fs.reverse) := by
  let first:=actual_chain_incidence_presentation leftClosed leftChain
  let second:=actual_chain_incidence_presentation rightClosed rightChain
  have length:=actual_chain_incidence_length_eq leftClosed rightClosed leftChain rightChain iso
  have order:=first.presentation.edge_lists_order_or_reverse second.presentation iso (fun e=>e.val.val) length
  rw [actual_edge_enum second] at order
  exact ⟨length,order⟩

theorem actual_chain_incidence_slot_order_or_reverse
    {left right : LTerm} {leftStart rightStart : Path} {es fs : List Path}
    (leftClosed : Closed left.erase) (rightClosed : Closed right.erase)
    (leftChain : PrerequisiteChain left leftStart es) (rightChain : PrerequisiteChain right rightStart fs)
    (iso : ChainIncidenceIso (chainSyntaxIncidence left leftClosed es) (chainSyntaxIncidence right rightClosed fs)) :
    let first:=actual_chain_incidence_presentation leftClosed leftChain
    let second:=actual_chain_incidence_presentation rightClosed rightChain
    es.length=fs.length ∧
      ((∀k,(second.presentation.edges.invFun (iso.edges (first.presentation.edges k))).val=k.val) ∨
       (∀k,(second.presentation.edges.invFun (iso.edges (first.presentation.edges k))).val=fs.length-1-k.val)) := by
  dsimp only
  let first:=actual_chain_incidence_presentation leftClosed leftChain
  let second:=actual_chain_incidence_presentation rightClosed rightChain
  have length:=actual_chain_incidence_length_eq leftClosed rightClosed leftChain rightChain iso
  have auxiliary {n m : Nat}
      (a : IndexedSimpleIncidencePath (chainSyntaxIncidence left leftClosed es) n)
      (b : IndexedSimpleIncidencePath (chainSyntaxIncidence right rightClosed fs) m) (equal : n=m) :
      (∀k,(b.edges.invFun (iso.edges (a.edges k))).val=k.val) ∨
      (∀k,(b.edges.invFun (iso.edges (a.edges k))).val=m-1-k.val) := by
    subst m;exact a.edge_order_or_reverse b iso
  exact ⟨length,auxiliary first.presentation second.presentation length⟩

private theorem edge_labelAt (term : LTerm) (edge : SyntaxIncidence.Edge term) :
    term.labelAt edge.val=some (SyntaxIncidence.label term edge) := by
  obtain ⟨node,lookup⟩ := SyntaxIncidence.edge_lookup term edge
  rw [LTerm.labelAt,lookup,Option.map_some,SyntaxIncidence.label_of_lookup term edge lookup]

theorem actual_chain_image_labels
    {left right : LTerm} {leftStart rightStart : Path} {es fs : List Path}
    (leftClosed : Closed left.erase) (rightClosed : Closed right.erase)
    (leftChain : PrerequisiteChain left leftStart es) (rightChain : PrerequisiteChain right rightStart fs)
    (iso : ChainIncidenceIso (chainSyntaxIncidence left leftClosed es) (chainSyntaxIncidence right rightClosed fs)) :
    (actualChainIsoImage leftClosed rightClosed leftChain rightChain iso).map right.labelAt=es.map left.labelAt := by
  let first:=actual_chain_incidence_presentation leftClosed leftChain
  apply List.ext_getElem (by simp only [actualChainIsoImage,List.length_map,List.length_ofFn])
  intro i hi hj
  have bound : i<es.length := by simpa only [List.length_map] using hj
  let k : Fin es.length := ⟨i,bound⟩
  simp only [List.getElem_map,actualChainIsoImage,List.getElem_ofFn]
  change right.labelAt (iso.edges (first.presentation.edges k)).val.val=left.labelAt (es.get k)
  rw [←first.edge_at k]
  rw [edge_labelAt,edge_labelAt]
  exact congrArg some (iso.label_eq (first.presentation.edges k)).symm

/-- Only the list direction is concluded. This neither pairs a first unsafe
ordinal in the forward orientation nor supplies a beta cut or suffix. -/
theorem actual_chain_label_order_or_reverse
    {left right : LTerm} {leftStart rightStart : Path} {es fs : List Path}
    (leftClosed : Closed left.erase) (rightClosed : Closed right.erase)
    (leftChain : PrerequisiteChain left leftStart es) (rightChain : PrerequisiteChain right rightStart fs)
    (iso : ChainIncidenceIso (chainSyntaxIncidence left leftClosed es) (chainSyntaxIncidence right rightClosed fs)) :
    es.map left.labelAt=fs.map right.labelAt ∨es.map left.labelAt=(fs.map right.labelAt).reverse := by
  have labels:=actual_chain_image_labels leftClosed rightClosed leftChain rightChain iso
  rcases (actual_chain_incidence_order_or_reverse leftClosed rightClosed leftChain rightChain iso).2 with same | reverse
  · rw [same] at labels;exact Or.inl labels.symm
  · rw [reverse,List.map_reverse] at labels;exact Or.inr labels.symm
end Lamping.AG
