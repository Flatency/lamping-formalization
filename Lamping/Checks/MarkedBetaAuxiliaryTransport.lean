import Lamping.Lamping.MarkedBetaAuxiliaryTransport
import Lamping.Checks.MarkedAuxiliaryPhysicalFixture

namespace Lamping.Checks.MarkedBetaAuxiliaryTransportChecks
open Graph Lambda Lambda.Labelled AG
open MarkedAuxiliaryPhysicalFixture

/-- The actual nonroot beta1 fixture has syntactic degree atom4. Arbitrary
SAME source and target selectors directly invoke NEW marked transport. -/
theorem direct_marked_physical_pair
    (sourceSelection : OccurrenceFragmentSelection original concrete.site.net (.inl ()))
    (targetSelection : OccurrenceFragmentSelection current concrete.site.reduce (.inl ()))
    (sourceJoint : JointRepresentation closed sourceSelection) :
    (targetSelection currentEdge).fragment.segments=(targetSelection currentEdge).fragment.segments := by
  obtain ⟨flow⟩:=source_flow
  obtain ⟨balance⟩:=source_indexed_balance
  exact concrete.site.beta_marked_auxiliary_pair initial (.nil _) (.nil _) (.nil _) closed
    source_matching source_inputs flow source_positive balance source_root_depth source_transparency
    relative normal history sourceSelection targetSelection sourceJoint redex physical_member at_degree
    currentEdge currentEdge auxiliary auxiliary rfl marked both_successful.1 both_successful.2

/-- SOURCEJoint is actually realized by the ORIGINAL canonical encoding and
its real corridor sourceIso, rather than an unproved history field. -/
theorem actual_source_joint_and_all_target_choices :
    ∃sourceSelection : OccurrenceFragmentSelection original concrete.site.net (.inl ()),
      JointRepresentation closed sourceSelection ∧
      ∀targetSelection : OccurrenceFragmentSelection current concrete.site.reduce (.inl ()),
        (targetSelection currentEdge).fragment.segments=(targetSelection currentEdge).fragment.segments := by
  obtain ⟨sourceSelection,joint⟩:=source_joint
  exact ⟨sourceSelection,joint,fun targetSelection=>direct_marked_physical_pair sourceSelection targetSelection joint⟩

/-- Actual target Matches supplies nonempty selectors; this is a genuine
physical direct consumer and a SELFPAIR, not distinct-pair/Joint truth. -/
theorem actual_nonempty_marked_physical_direct :
    ∃sourceSelection : OccurrenceFragmentSelection original concrete.site.net (.inl ()),
      ∃targetSelection : OccurrenceFragmentSelection current concrete.site.reduce (.inl ()),
        JointRepresentation closed sourceSelection ∧
        (targetSelection currentEdge).fragment.segments=(targetSelection currentEdge).fragment.segments := by
  obtain ⟨sourceSelection,joint⟩:=source_joint
  obtain ⟨targetSelection⟩:=target_matches.occurrence_fragment_selection currentClosed
  exact ⟨sourceSelection,targetSelection,joint,direct_marked_physical_pair sourceSelection targetSelection joint⟩

theorem actual_same_INIT_step_fiber_history : INIT original ∧
    GraphStep (.beta 1) (ActualNet.initial term) (ActualNet.ofNet concrete.site.reduce) ∧
    concrete.site.betaSyntaxFiber (.inl ()) original.erase=[[.arg]] ∧
    original.degreeAt redex.val=some (Lambda.Labelled.Label.atom 4) ∧
    History [[.arg]] original current ∧
    Marked.RelativeHistory [[.arg]] (Marked.mark (concrete.site.betaSyntaxFiber (.inl ()) original.erase) original.erase) endpoint ∧
    Marked.Normal endpoint :=
  ⟨initial,actual_beta_step,exact_fiber,at_degree,history,relative,normal⟩

#print axioms direct_marked_physical_pair
#print axioms actual_source_joint_and_all_target_choices
#print axioms actual_nonempty_marked_physical_direct
#print axioms actual_same_INIT_step_fiber_history
#print axioms MarkedAuxiliaryPhysicalFixture.actual_marked_word
#print axioms MarkedAuxiliaryPhysicalFixture.both_successful
#print axioms MarkedAuxiliaryPhysicalFixture.target_matches
end Lamping.Checks.MarkedBetaAuxiliaryTransportChecks
