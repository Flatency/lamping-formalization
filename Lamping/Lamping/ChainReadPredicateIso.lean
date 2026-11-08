import Lamping.Lamping.ChainSyntaxIncidence
namespace Lamping.AG
open Lambda Lambda.Labelled

/-- A bare iso matches the label at each supplied selected edge to a genuine
edge occurrence. It makes no assertion about its list ordinal or read sign. -/
theorem ChainIncidenceIso.read_label_preimage
    {left right node : LTerm} {leftClosed : Closed left.erase} {rightClosed : Closed right.erase}
    {leftEdges rightEdges : List Path} {edge : Path}
    (iso : ChainIncidenceIso (chainSyntaxIncidence left leftClosed leftEdges)
      (chainSyntaxIncidence right rightClosed rightEdges))
    (member : edge∈rightEdges) (lookup : right.subterm edge=some node) :
    ∃oldEdge oldNode,oldEdge∈leftEdges ∧left.subterm oldEdge=some oldNode ∧oldNode.label=node.label := by
  let selected : (chainSyntaxIncidence right rightClosed rightEdges).Edge :=
    ⟨⟨edge,by rw [←LTerm.erase_subterm,lookup];rfl⟩,member⟩
  let original := iso.edges.invFun selected
  obtain ⟨oldNode,oldLookup⟩ := SyntaxIncidence.edge_lookup left original.val
  have same := iso.label_eq original
  rw [iso.edges.right_inv] at same
  change SyntaxIncidence.label left original.val=SyntaxIncidence.label right selected.val at same
  rw [SyntaxIncidence.label_of_lookup left original.val oldLookup,
    SyntaxIncidence.label_of_lookup right selected.val lookup] at same
  exact ⟨original.val.val,oldNode,original.property,oldLookup,same⟩

/-- Universal READ-label properties, including marker safety, are invariant
under bare incidence iso. This does not match the first unsafe ordinal. -/
theorem ChainIncidenceIso.read_predicate_iff
    {left right : LTerm} {leftClosed : Closed left.erase} {rightClosed : Closed right.erase}
    {leftEdges rightEdges : List Path}
    (iso : ChainIncidenceIso (chainSyntaxIncidence left leftClosed leftEdges)
      (chainSyntaxIncidence right rightClosed rightEdges)) (predicate : Label → Prop) :
    (∀edge∈leftEdges,∀node,left.subterm edge=some node →predicate node.label) ↔
    (∀edge∈rightEdges,∀node,right.subterm edge=some node →predicate node.label) := by
  constructor
  · intro all edge member node lookup
    obtain ⟨oldEdge,oldNode,inside,atOld,same⟩ := iso.read_label_preimage member lookup
    exact same ▸ all oldEdge inside oldNode atOld
  · intro all edge member node lookup
    obtain ⟨oldEdge,oldNode,inside,atOld,same⟩ := iso.symm.read_label_preimage member lookup
    exact same ▸ all oldEdge inside oldNode atOld

#print axioms ChainIncidenceIso.read_label_preimage
#print axioms ChainIncidenceIso.read_predicate_iff
end Lamping.AG
