import Lamping.Graph.Core
import Lamping.Lambda.Labels

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

/-- A directed edge-labelled incidence structure. It makes no finiteness,
path, syntax-origin or representation-correctness assertion. -/
structure EdgeLabelledIncidence where
  Vertex : Type
  Edge : Type
  source : Edge → Vertex
  target : Edge → Vertex
  label : Edge → Labelled.Label

/-- Bare directed incidence isomorphism. There is no distinguished chase
start or reading sign, nor extra node-sort/port preservation hypothesis.
Relating this precise object to AG's chain isomorphism remains a theorem. -/
structure ChainIncidenceIso (left right : EdgeLabelledIncidence) where
  vertices : Bij left.Vertex right.Vertex
  edges : Bij left.Edge right.Edge
  source_eq : ∀ edge,vertices (left.source edge)=right.source (edges edge)
  target_eq : ∀ edge,vertices (left.target edge)=right.target (edges edge)
  label_eq : ∀ edge,left.label edge=right.label (edges edge)

def ChainIncidenceIso.refl (graph : EdgeLabelledIncidence) : ChainIncidenceIso graph graph where
  vertices := Bij.refl _
  edges := Bij.refl _
  source_eq := fun _=>rfl
  target_eq := fun _=>rfl
  label_eq := fun _=>rfl

def ChainIncidenceIso.symm (iso : ChainIncidenceIso left right) : ChainIncidenceIso right left where
  vertices := iso.vertices.symm
  edges := iso.edges.symm
  source_eq := by
    intro edge
    have preserved := iso.source_eq (iso.edges.invFun edge)
    rw [iso.edges.right_inv] at preserved
    have inverse := congrArg iso.vertices.invFun preserved
    simpa only [Bij.symm,iso.vertices.left_inv] using inverse.symm
  target_eq := by
    intro edge
    have preserved := iso.target_eq (iso.edges.invFun edge)
    rw [iso.edges.right_inv] at preserved
    have inverse := congrArg iso.vertices.invFun preserved
    simpa only [Bij.symm,iso.vertices.left_inv] using inverse.symm
  label_eq := by
    intro edge
    have preserved := iso.label_eq (iso.edges.invFun edge)
    rw [iso.edges.right_inv] at preserved
    exact preserved.symm

def ChainIncidenceIso.trans (first : ChainIncidenceIso left middle)
    (second : ChainIncidenceIso middle right) : ChainIncidenceIso left right where
  vertices := first.vertices.trans second.vertices
  edges := first.edges.trans second.edges
  source_eq := by
    intro edge
    change second.vertices (first.vertices (left.source edge))=
      right.source (second.edges (first.edges edge))
    rw [first.source_eq,second.source_eq]
  target_eq := by
    intro edge
    change second.vertices (first.vertices (left.target edge))=
      right.target (second.edges (first.edges edge))
    rw [first.target_eq,second.target_eq]
  label_eq := fun edge=>(first.label_eq edge).trans (second.label_eq (first.edges edge))

def ChainIncidenceIsomorphic (left right : EdgeLabelledIncidence) : Prop :=
  Nonempty (ChainIncidenceIso left right)

end Lamping.AG
namespace Lamping.AG
open Graph

def EdgeLabelledIncidence.Incident (graph : EdgeLabelledIncidence)
    (selected : graph.Edge → Prop) (vertex : graph.Vertex) : Prop :=
  ∃ edge,selected edge ∧(vertex=graph.source edge ∨vertex=graph.target edge)

/-- Edge-induced subgraph; equal labels never identify actual edge ids. The empty selection yields empty carriers. -/
def EdgeLabelledIncidence.induced (graph : EdgeLabelledIncidence)
    (selected : graph.Edge → Prop) : EdgeLabelledIncidence where
  Vertex := {vertex : graph.Vertex // graph.Incident selected vertex}
  Edge := {edge : graph.Edge // selected edge}
  source := fun edge=>⟨graph.source edge.val,edge.val,edge.property,Or.inl rfl⟩
  target := fun edge=>⟨graph.target edge.val,edge.val,edge.property,Or.inr rfl⟩
  label := fun edge=>graph.label edge.val

/-- Restriction requires exact two-sided correspondence of selected edge ids. It does not assert a REP invariant. -/
def ChainIncidenceIso.restrict (iso : ChainIncidenceIso left right)
    (selectedLeft : left.Edge → Prop) (selectedRight : right.Edge → Prop)
    (correspond : ∀ edge,selectedLeft edge ↔selectedRight (iso.edges edge)) :
    ChainIncidenceIso (left.induced selectedLeft) (right.induced selectedRight) := by
  let edgeTo : {e //selectedLeft e} →{e //selectedRight e} := fun edge=>
    ⟨iso.edges edge.val,(correspond edge.val).mp edge.property⟩
  let edgeFrom : {e //selectedRight e} →{e //selectedLeft e} := fun edge=>
    ⟨iso.edges.invFun edge.val,(correspond _).mpr (by
      rw [iso.edges.right_inv]; exact edge.property)⟩
  let vertexTo : {v //left.Incident selectedLeft v} →{v //right.Incident selectedRight v} := by
    intro vertex
    refine ⟨iso.vertices vertex.val,?_⟩
    obtain ⟨edge,selected,endpoint⟩ := vertex.property
    refine ⟨iso.edges edge,(correspond edge).mp selected,?_⟩
    rcases endpoint with source | target
    · exact .inl (by rw [source]; exact iso.source_eq edge)
    · exact .inr (by rw [target]; exact iso.target_eq edge)
  let vertexFrom : {v //right.Incident selectedRight v} →{v //left.Incident selectedLeft v} := by
    intro vertex
    refine ⟨iso.vertices.invFun vertex.val,?_⟩
    obtain ⟨edge,selected,endpoint⟩ := vertex.property
    refine ⟨iso.edges.invFun edge,(correspond _).mpr ?_,?_⟩
    · rw [iso.edges.right_inv]; exact selected
    · rcases endpoint with source | target
      · exact .inl (by rw [source]; exact iso.symm.source_eq edge)
      · exact .inr (by rw [target]; exact iso.symm.target_eq edge)
  exact {
    vertices := ⟨vertexTo,vertexFrom,
      fun vertex=>Subtype.ext (iso.vertices.left_inv vertex.val),
      fun vertex=>Subtype.ext (iso.vertices.right_inv vertex.val)⟩
    edges := ⟨edgeTo,edgeFrom,
      fun edge=>Subtype.ext (iso.edges.left_inv edge.val),
      fun edge=>Subtype.ext (iso.edges.right_inv edge.val)⟩
    source_eq := fun edge=>Subtype.ext (iso.source_eq edge.val)
    target_eq := fun edge=>Subtype.ext (iso.target_eq edge.val)
    label_eq := fun edge=>iso.label_eq edge.val }
end Lamping.AG