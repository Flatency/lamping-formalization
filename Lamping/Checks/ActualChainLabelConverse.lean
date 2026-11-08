import Lamping.Lamping.ActualChainLabelConverse
import Lamping.Checks.ActualChainForwardOrder
namespace Lamping.Checks.ActualChainLabelConverseChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence
namespace Distinct
open ActualChainForwardOrderChecks.Distinct

theorem direct_actual_labels : leftEdges.map current.labelAt=rightEdges.map current.labelAt := rfl

/-- No supplied incidence iso is used: the actual different-copy full label
vectors alone feed the converse under the real original INIT/history. -/
theorem actual_noninit_distinct_converse :
    ChainIncidenceIsomorphic (chainSyntaxIncidence current closedCurrent leftEdges)
      (chainSyntaxIncidence current closedCurrent rightEdges) :=
  actual_chain_iso_of_labels history initial closedCurrent leftChain rightChain direct_actual_labels

theorem actual_noninit_and_different : INIT original ∧History [[]] original current ∧¬INIT current ∧
    leftStart≠rightStart ∧leftEdges≠rightEdges := actual_noninit_same_origin

theorem returned_iso_has_forward_edges : ∃iso :
    ChainIncidenceIso (chainSyntaxIncidence current closedCurrent leftEdges)
      (chainSyntaxIncidence current closedCurrent rightEdges),
    actualChainIsoImage closedCurrent closedCurrent leftChain rightChain iso=rightEdges := by
  obtain ⟨iso⟩:=actual_noninit_distinct_converse
  exact ⟨iso,(actual_chain_incidence_forward history initial closedCurrent leftChain rightChain iso).2⟩

theorem actual_variable_binder : current.subterm [.fn,.fn,.body,.fn]=some (.var (.atom 8) 0) ∧
    current.subterm [.arg,.fn,.body,.fn]=some (.var (.atom 8) 0) := ⟨rfl,rfl⟩
end Distinct
namespace Terminal
open DirectedReadingDecompositionChecks
abbrev closedTarget : Closed target.erase := history.closed closed

theorem actual_terminal_converse :
    ChainIncidenceIsomorphic (chainSyntaxIncidence target closedTarget [[.fn]])
      (chainSyntaxIncidence target closedTarget [[.fn]]) :=
  actual_chain_iso_of_labels history initial closedTarget successful_function successful_context rfl

theorem actual_opposite_readings : PrerequisiteReadsDirected target [] [.fn] true ∧
    PrerequisiteReadsDirected target [.fn] [.fn] false :=
  ⟨⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩,⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩⟩

theorem actual_vertex_reverse_retained :
    ∀k,(IndexedSimpleIncidencePath.mappedSlot
      ActualChainPathPresentationsChecks.Singleton.appPath.presentation
      ActualChainPathPresentationsChecks.Singleton.lamPath.presentation (ChainIncidenceIso.refl _) k).val=1-k.val :=
  ActualChainPathPresentationsChecks.Singleton.actual_forced_reverse
end Terminal
#print axioms Source.actual_kind
#print axioms Target.actual_kind
#print axioms History.equal_label_endpoint_kinds
#print axioms PrerequisiteChain.signed_path
#print axioms SignedProperWalk.signs_eq_of_multiedge
#print axioms ProperIncidenceWalk.vertices_unique
#print axioms IndexedSimpleIncidencePath.isoOfOrientations
#print axioms actual_multichain_iso_of_labels
#print axioms actual_chain_iso_of_labels
#print axioms actual_chain_iso_iff_labels
#print axioms Distinct.direct_actual_labels
#print axioms Distinct.actual_noninit_distinct_converse
#print axioms Distinct.actual_noninit_and_different
#print axioms Distinct.returned_iso_has_forward_edges
#print axioms Distinct.actual_variable_binder
#print axioms Terminal.actual_terminal_converse
#print axioms Terminal.actual_opposite_readings
#print axioms Terminal.actual_vertex_reverse_retained
end Lamping.Checks.ActualChainLabelConverseChecks
