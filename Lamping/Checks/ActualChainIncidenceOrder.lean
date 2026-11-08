import Lamping.Lamping.ActualChainIncidenceOrder
import Lamping.Checks.ActualChainPathPresentations
namespace Lamping.Checks.ActualChainIncidenceOrderChecks
open Graph Lambda Lambda.Labelled AG
namespace Singleton
open DirectedReadingDecompositionChecks
abbrev closedTarget : Closed target.erase := history.closed closed
theorem actual_opposite_starts_edge_order :
    [[Step.fn]].length=[[Step.fn]].length ∧
    (actualChainIsoImage closedTarget closedTarget successful_function successful_context (ChainIncidenceIso.refl _)=[[.fn]] ∨
      actualChainIsoImage closedTarget closedTarget successful_function successful_context (ChainIncidenceIso.refl _)=[[.fn]].reverse) :=
  actual_chain_incidence_order_or_reverse closedTarget closedTarget successful_function successful_context (ChainIncidenceIso.refl _)
theorem actual_opposite_starts_label_order :
    [[.fn]].map target.labelAt=[[.fn]].map target.labelAt ∨
      [[.fn]].map target.labelAt=([[.fn]].map target.labelAt).reverse :=
  actual_chain_label_order_or_reverse closedTarget closedTarget successful_function successful_context (ChainIncidenceIso.refl _)
theorem actual_vertex_reversal_remains :
    ∀k,(IndexedSimpleIncidencePath.mappedSlot
      ActualChainPathPresentationsChecks.Singleton.appPath.presentation
      ActualChainPathPresentationsChecks.Singleton.lamPath.presentation (ChainIncidenceIso.refl _) k).val=1-k.val :=
  ActualChainPathPresentationsChecks.Singleton.actual_forced_reverse
end Singleton

namespace Multiple
open WrappedSuccessfulChains
noncomputable abbrev comparison := ChainIncidenceIso.refl (chainSyntaxIncidence current targetClosed bodyEdges)
theorem actual_two_edge_order : bodyEdges.length=bodyEdges.length ∧
    (actualChainIsoImage targetClosed targetClosed body_chain body_chain comparison=bodyEdges ∨
     actualChainIsoImage targetClosed targetClosed body_chain body_chain comparison=bodyEdges.reverse) :=
  actual_chain_incidence_order_or_reverse targetClosed targetClosed body_chain body_chain comparison
theorem actual_two_edge_labels : bodyEdges.map current.labelAt=bodyEdges.map current.labelAt ∨
    bodyEdges.map current.labelAt=(bodyEdges.map current.labelAt).reverse :=
  actual_chain_label_order_or_reverse targetClosed targetClosed body_chain body_chain comparison

theorem actual_two_edge_image_forward :
    actualChainIsoImage targetClosed targetClosed body_chain body_chain comparison=bodyEdges := by
  apply List.ext_getElem (by simp only [actualChainIsoImage,List.length_ofFn])
  intro i hi hj
  simp only [actualChainIsoImage,List.getElem_ofFn,comparison,ChainIncidenceIso.refl,Bij.refl]
  exact (actual_chain_incidence_presentation targetClosed body_chain).edge_at ⟨i,hj⟩

theorem actual_two_edge_reverse_rejected :
    actualChainIsoImage targetClosed targetClosed body_chain body_chain comparison≠bodyEdges.reverse := by
  rw [actual_two_edge_image_forward]
  decide

theorem actual_singleton_twoedge_no_iso :
    ¬ChainIncidenceIsomorphic (chainSyntaxIncidence current targetClosed rootEdges)
      (chainSyntaxIncidence current targetClosed bodyEdges) := by
  rintro ⟨iso⟩
  have length:=actual_chain_incidence_length_eq targetClosed targetClosed root_chain body_chain iso
  cases length

theorem actual_same_initial_multiedge : INIT original ∧History [[.fn]] original current ∧
    PrerequisiteChain current bodyApp bodyEdges := ⟨initial,actualHistory,body_chain⟩
end Multiple

#print axioms finite_bij_length_eq
#print axioms actual_chain_incidence_length_eq
#print axioms IndexedSimpleIncidencePath.edge_order_or_reverse
#print axioms actual_chain_incidence_slot_order_or_reverse
#print axioms actual_chain_incidence_order_or_reverse
#print axioms actual_chain_image_labels
#print axioms actual_chain_label_order_or_reverse
#print axioms Singleton.actual_opposite_starts_edge_order
#print axioms Singleton.actual_vertex_reversal_remains
#print axioms Multiple.actual_two_edge_order
#print axioms Multiple.actual_two_edge_labels
#print axioms Multiple.actual_two_edge_image_forward
#print axioms Multiple.actual_two_edge_reverse_rejected
#print axioms Multiple.actual_singleton_twoedge_no_iso
#print axioms Multiple.actual_same_initial_multiedge
end Lamping.Checks.ActualChainIncidenceOrderChecks
