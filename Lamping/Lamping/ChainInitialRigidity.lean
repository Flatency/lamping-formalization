import Lamping.Lamping.ChainSyntaxIncidence
import Lamping.Lambda.DegreeFamily

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

/-- An induced labelled subgraph isomorphism on the same ambient graph
fixes actual edge ids when the ambient labels distinguish them. No claim
about an isomorphism of noninitial repeated-label graphs follows. -/
theorem ChainIncidenceIso.induced_edges_fixed
    {graph : EdgeLabelledIncidence} {left right : graph.Edge → Prop}
    (distinct : ∀ a b,graph.label a=graph.label b → a=b)
    (iso : ChainIncidenceIso (graph.induced left) (graph.induced right))
    (edge : (graph.induced left).Edge) : (iso.edges edge).val=edge.val := by
  exact distinct _ _ (iso.label_eq edge).symm

theorem ChainIncidenceIso.induced_selected_iff
    {graph : EdgeLabelledIncidence} {left right : graph.Edge → Prop}
    (distinct : ∀ a b,graph.label a=graph.label b → a=b)
    (iso : ChainIncidenceIso (graph.induced left) (graph.induced right)) :
    ∀ edge,left edge ↔right edge := by
  intro edge
  constructor
  · intro selected
    have fixed := iso.induced_edges_fixed distinct ⟨edge,selected⟩
    have kept := (iso.edges ⟨edge,selected⟩).property
    change right ((iso.edges ⟨edge,selected⟩).val) at kept
    rw [fixed] at kept
    exact kept
  · intro selected
    have fixed := iso.symm.induced_edges_fixed distinct ⟨edge,selected⟩
    have kept := (iso.edges.invFun ⟨edge,selected⟩).property
    change left ((iso.symm.edges ⟨edge,selected⟩).val) at kept
    rw [fixed] at kept
    exact kept

/-- Nodup of actual syntax labels, rather than atomicity, is the precise
initial-only input required here. -/
theorem syntaxIncidence_label_injective (current : LTerm) (distinct : current.labels.Nodup)
    (left right : SyntaxIncidence.Edge current)
    (same : SyntaxIncidence.label current left=SyntaxIncidence.label current right) : left=right := by
  obtain ⟨a,atLeft⟩ := SyntaxIncidence.edge_lookup current left
  obtain ⟨b,atRight⟩ := SyntaxIncidence.edge_lookup current right
  rw [SyntaxIncidence.label_of_lookup current left atLeft,
    SyntaxIncidence.label_of_lookup current right atRight] at same
  exact Subtype.ext (LTerm.subterm_label_injective current distinct atLeft atRight same)

/-- In one actual INIT term, bare incidence isomorphism already forces
identical selected syntax edge occurrences. This is only an initial bridge;
no general-history REP or port-preservation assertion is embedded in it. -/
theorem chainSyntaxIncidence_initial_selected_iff
    (current : LTerm) (closed : Closed current.erase) (initial : INIT current)
    (left right : List Path)
    (iso : ChainIncidenceIso (chainSyntaxIncidence current closed left)
      (chainSyntaxIncidence current closed right)) :
    ∀ edge : SyntaxIncidence.Edge current,edge.val∈left ↔edge.val∈right := by
  exact iso.induced_selected_iff (syntaxIncidence_label_injective current initial.2)

end Lamping.AG
