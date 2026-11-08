import Lamping.Lamping.FamilyRepresentation
import Lamping.Lambda.DegreeFamily
namespace Lamping.AG
open Graph Lambda Lambda.Labelled

/-- A non-loop singleton induced graph is determined by its edge label. -/
noncomputable def EdgeLabelledIncidence.singleton_iso
    (left right : EdgeLabelledIncidence) (e : left.Edge) (f : right.Edge)
    (leftDistinct : left.source e≠left.target e)
    (rightDistinct : right.source f≠right.target f)
    (same : left.label e=right.label f) :
    ChainIncidenceIso (left.induced (fun x=>x=e)) (right.induced (fun x=>x=f)) := by
  classical
  let L := left.induced (fun x=>x=e)
  let R := right.induced (fun x=>x=f)
  have leftCases (v : L.Vertex) : v.val=left.source e ∨v.val=left.target e := by
    obtain ⟨edge,selected,incident⟩ := v.property
    subst edge
    exact incident
  have rightCases (v : R.Vertex) : v.val=right.source f ∨v.val=right.target f := by
    obtain ⟨edge,selected,incident⟩ := v.property
    subst edge
    exact incident
  let forward (v : L.Vertex) : R.Vertex :=
    if v.val=left.source e then ⟨right.source f,f,rfl,Or.inl rfl⟩
    else ⟨right.target f,f,rfl,Or.inr rfl⟩
  let backward (v : R.Vertex) : L.Vertex :=
    if v.val=right.source f then ⟨left.source e,e,rfl,Or.inl rfl⟩
    else ⟨left.target e,e,rfl,Or.inr rfl⟩
  refine {
    vertices := {toFun:=forward,invFun:=backward,left_inv:=?_,right_inv:=?_}
    edges := {
      toFun := fun _=>⟨f,rfl⟩
      invFun := fun _=>⟨e,rfl⟩
      left_inv := by rintro ⟨edge,rfl⟩;rfl
      right_inv := by rintro ⟨edge,rfl⟩;rfl }
    source_eq := ?_
    target_eq := ?_
    label_eq := ?_ }
  · intro v
    apply Subtype.ext
    rcases leftCases v with first|second
    · simp [forward,backward,first]
    · simp [forward,backward,second,leftDistinct.symm,rightDistinct.symm]
  · intro v
    apply Subtype.ext
    rcases rightCases v with first|second
    · simp [forward,backward,first]
    · simp [forward,backward,second,leftDistinct.symm,rightDistinct.symm]
  · rintro ⟨edge,rfl⟩
    apply Subtype.ext
    simp [forward,L,R,EdgeLabelledIncidence.induced]
  · rintro ⟨edge,rfl⟩
    apply Subtype.ext
    simp [forward,L,R,EdgeLabelledIncidence.induced,leftDistinct.symm]
  · rintro ⟨edge,rfl⟩
    exact same
private def redexFunctionPosition {current : LTerm}
    (lookup : current.subterm p=some (.app appStamp (.lam lamStamp body) arg)) :
    SyntaxIncidence.Edge current :=
  ⟨p++[.fn],by
    rw [←LTerm.erase_subterm,LTerm.subterm_append,lookup]
    rfl⟩

private theorem redex_child_lookup {current : LTerm}
    (lookup : current.subterm p=some (.app appStamp (.lam lamStamp body) arg)) :
    current.subterm (p++[.fn])=some (.lam lamStamp body) := by
  rw [LTerm.subterm_append,lookup];rfl

private theorem redex_edge_nonloop {current : LTerm} (closed : Closed current.erase)
    (lookup : current.subterm p=some (.app appStamp (.lam lamStamp body) arg)) :
    (syntaxIncidenceGraph current closed).source (redexFunctionPosition lookup)≠
      (syntaxIncidenceGraph current closed).target (redexFunctionPosition lookup) := by
  let edge := redexFunctionPosition lookup
  let parent : SyntaxIncidence.ProperPosition current :=
    ⟨p,Or.inl ⟨appStamp,.lam lamStamp body,arg,lookup⟩⟩
  let child : SyntaxIncidence.ProperPosition current :=
    ⟨p++[.fn],Or.inr ⟨lamStamp,body,redex_child_lookup lookup⟩⟩
  have source : SyntaxIncidence.source current edge=some parent :=
    SyntaxIncidence.source_eq_of_spec current edge ⟨.fn,_,.appFn appStamp,rfl,lookup,.fn⟩
  have target : SyntaxIncidence.target current closed edge=some child :=
    SyntaxIncidence.target_eq_of_spec current closed edge (Or.inl rfl)
  change SyntaxIncidence.source current edge≠SyntaxIncidence.target current closed edge
  rw [source,target]
  intro equal
  have paths := congrArg (fun v : SyntaxIncidence.Vertex current=>v.map (fun x=>x.val)) equal
  have literal : p=p++[.fn] := Option.some.inj paths
  have sizes := congrArg List.length literal
  simp only [List.length_append,List.length_singleton] at sizes
  omega

private theorem selected_singleton {current : LTerm}
    (lookup : current.subterm p=some (.app appStamp (.lam lamStamp body) arg))
    (edge : SyntaxIncidence.Edge current) :
    edge.val∈[p++[.fn]] ↔edge=redexFunctionPosition lookup := by
  simp only [List.mem_singleton]
  constructor
  · intro same;apply Subtype.ext;exact same
  · intro same;exact congrArg Subtype.val same

theorem redex_chain_iso_iff_degree {current : LTerm} (closed : Closed current.erase)
    (first : current.subterm p=some (.app appStamp (.lam lamStamp body) arg))
    (second : current.subterm q=some (.app otherApp (.lam otherLam otherBody) otherArg)) :
    ChainIncidenceIsomorphic (chainSyntaxIncidence current closed [p++[.fn]])
      (chainSyntaxIncidence current closed [q++[.fn]]) ↔current.degreeAt p=current.degreeAt q := by
  let graph := syntaxIncidenceGraph current closed
  let leftEdge := redexFunctionPosition first
  let rightEdge := redexFunctionPosition second
  let leftNormal := (ChainIncidenceIso.refl graph).restrict
    (fun edge=>edge.val∈[p++[Step.fn]]) (fun edge=>edge=leftEdge) (fun edge=>by
      change edge.val∈[p++[Step.fn]] ↔edge=leftEdge
      exact selected_singleton first edge)
  let rightNormal := (ChainIncidenceIso.refl graph).restrict
    (fun edge=>edge.val∈[q++[Step.fn]]) (fun edge=>edge=rightEdge) (fun edge=>by
      change edge.val∈[q++[Step.fn]] ↔edge=rightEdge
      exact selected_singleton second edge)
  have leftLabel : graph.label leftEdge=lamStamp :=
    SyntaxIncidence.label_of_lookup current leftEdge (redex_child_lookup first)
  have rightLabel : graph.label rightEdge=otherLam :=
    SyntaxIncidence.label_of_lookup current rightEdge (redex_child_lookup second)
  have degrees : current.degreeAt p=current.degreeAt q ↔lamStamp=otherLam := by
    simp only [LTerm.degreeAt,first,second,Option.bind_some,LTerm.degree,Option.some.injEq]
  constructor
  · rintro ⟨iso⟩
    let normalized := leftNormal.symm.trans (iso.trans rightNormal)
    have labels := normalized.label_eq ⟨leftEdge,rfl⟩
    have atRight : (normalized.edges ⟨leftEdge,rfl⟩).val=rightEdge :=
      (normalized.edges ⟨leftEdge,rfl⟩).property
    change graph.label leftEdge=graph.label (normalized.edges ⟨leftEdge,rfl⟩).val at labels
    rw [atRight,leftLabel,rightLabel] at labels
    exact degrees.mpr labels
  · intro same
    have labels : graph.label leftEdge=graph.label rightEdge :=
      leftLabel.trans ((degrees.mp same).trans rightLabel.symm)
    exact ⟨leftNormal.trans ((graph.singleton_iso graph leftEdge rightEdge
      (redex_edge_nonloop closed first) (redex_edge_nonloop closed second) labels).trans rightNormal.symm)⟩

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

/-- REP identifies redex function-edge representations by the current degree.
It is a conditional consequence of REP, without an INIT assumption on reducts. -/
theorem redex_chain_representation_iff_degree (closed : Closed current.erase)
    (selection : OccurrenceFragmentSelection current g root)
    (representation : ChainRepresentationInvariant closed selection)
    (first : current.subterm p=some (.app appStamp (.lam lamStamp body) arg))
    (second : current.subterm q=some (.app otherApp (.lam otherLam otherBody) otherArg)) :
    SameChainRepresentation selection (PrerequisiteChain.redex_app first)
      (PrerequisiteChain.redex_app second) ↔current.degreeAt p=current.degreeAt q :=
  (representation _ _).trans (redex_chain_iso_iff_degree closed first second)
end

end Lamping.AG
